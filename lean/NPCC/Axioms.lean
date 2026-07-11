import Mathlib

/-! # Project citation interface

The development has exactly one project-level citation axiom beyond Lean's
standard kernel axioms: the finite-alphabet balanced-family corollary below.
The VBP endpoint formerly tracked as `vbp_np_hard` has been discharged in
`NPCC.Wrapper`, so it is not declared here or allowed as a citation axiom.

The attribution is deliberately precise. Alon--Goldreich--Hastad--Peralta
(1992) construct almost-wise-independent spaces over binary strings. The exact
interface used here has an arbitrary finite alphabet, relative pointwise error,
an indexed multiset, and one uniform polynomial-size bound. That formulation is
obtained by applying the derandomized Chernoff-with-union-bound sampler of
Bshouty (ECCC TR16-083, Corollary 3) to the cylinder events in `Y ^ q`; Bshouty
explicitly records the extension to arbitrary alphabets and product
distributions. `docs/BALANCED-FAMILY-CITATION.md` spells out the parameter
translation. Thus the axiom is a citation boundary for that corollary, not a
claim that the displayed statement appears verbatim in AGHP. -/

namespace NPCC

-- CLAIM-BEGIN axiom:aghp
/-- CITATION INTERFACE for the finite-alphabet balanced-family corollary used
by the paper's `rem:balanced-columns-exist`.

This is the exact existence-and-size statement consumed by the Lean proof:
for every nonempty finite alphabet `Y`, it supplies an indexed family of
`q`-tuples (repetitions are counted) with relative pointwise error at most
`epsilon` on every projection of size at most `t`. One absolute constant also
bounds the family size by the displayed expression.

Source chain: AGHP supplies the historical binary almost-independence
construction; Bshouty's generic sampler and arbitrary-alphabet extension give
this exact corollary. The Lean development treats that external construction
theorem as an assumption. Deterministic polynomial-time generation is not part
of this proposition, so this axiom is not itself an executable generator. -/
axiom finite_alphabet_balanced_family_exists :
    ∃ C : ℕ, 0 < C ∧
      ∀ (q t : ℕ) (Y : Type) [Fintype Y] [DecidableEq Y] (ε : ℝ),
        1 ≤ t → t ≤ q → 0 < ε → ε < 1 → 1 ≤ Fintype.card Y →
        ∃ (L : ℕ) (S : Fin L → Fin q → Y),
          0 < L ∧
          (L : ℝ) ≤ ((q + 2 : ℕ) : ℝ) ^ C * ((Fintype.card Y + 2 : ℕ) : ℝ) ^ (C * t)
                      * ((⌈1 / ε⌉₊ : ℕ) : ℝ) ^ C ∧
          ∀ J : Finset (Fin q), J.card ≤ t → ∀ a : Fin q → Y,
            |((Finset.univ.filter
                  (fun j : Fin L => ∀ γ ∈ J, S j γ = a γ)).card : ℝ) / (L : ℝ)
              - 1 / (Fintype.card Y : ℝ) ^ J.card|
            ≤ ε / (Fintype.card Y : ℝ) ^ J.card
-- CLAIM-END axiom:aghp

end NPCC
