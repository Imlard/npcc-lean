import Mathlib
import NPCC.Scaffold
import NPCC.Gadget
import NPCC.VBP

/-! # Explicit output-carrier bounds

This module proves exact cardinalities and closed-form upper bounds for the row
and column carriers of `M₄`:

* `|R₄| = 4·|C₂| + n = 4·L₂(d) + n`  (`card_R4`)
* `|C₄| = 32·|R₂|⁴ = 32·(q₂(d)·L₁(d))⁴`  (`card_C4`)

The balanced-family axiom's explicit size clause
`L ≤ (q+2)^C · (|Y|+2)^{C·t} · ⌈1/ε⌉^C` (`NPCC.finite_alphabet_balanced_family_exists`,
`NPCC.Axioms`) bounds the two balanced-family sizes `L₁(d)`, `L₂(d)` by
explicit monomials in the scaffold parameters `q₁,q₂,t₁,t₂` (all exact ℕ
functions of `Nat.log 2 d`). Composing gives `output_size_bounds`:
`|R₄| ≤ n + P_R(d)` and `|C₄| ≤ P_C(d)` with `P_R`, `P_C` the explicit
closed-form expressions `rowPoly d`, `colPoly d` below.

The gate hypotheses (`t₁ ≤ q₁+5`, `t₂ ≤ q₂`, `1 ≤ q₁`) are exactly the
large-`d` side conditions the balanced families are already exposed under
(`S1fam_balanced`, `S2fam_balanced`); on the reduction's normalised
power-of-two regime `d ≥ d_star` they hold (`LargeD.lean`). They are carried
as hypotheses here so the size lemma remains regime-agnostic.

This is a carrier-count theorem, not a Turing-machine runtime theorem.
`NPCC.PolynomialSize` proves its fixed-degree domination in the combinatorial
source size. Square power-of-two padding and its polynomial bit-count bound are
proved separately in `NPCC.Padding` and `NPCC.Public`. -/

namespace NPCC

open Workspace.Types.Interlace

/-! ## Exact carrier cardinalities -/

/-- Exact row count of `M₄`: `|R₄| = |R₃| + n = 4·|C₂| + n = 4·L₂(d) + n`.
`R₄ = R₃ ⊕ [n]` (tagged sum), `R₃ = [4] × C₂`, `C₂ = Fin (L₂ d)`. -/
theorem card_R4 (d n : ℕ) : Fintype.card (R4 d n) = 4 * L2 d + n := by
  simp [R4, R3, C2, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
        mul_comm]

/-- Exact column count of `M₄`: `|C₄| = 2⁵·|C₃| = 32·|R₂|⁴ = 32·(q₂(d)·L₁(d))⁴`.
`C₄ = [2⁵] × C₃`, `C₃ = [4] → R₂`, `R₂ = [q₂] × C₁`, `C₁ = Fin (L₁ d)`. -/
theorem card_C4 (d : ℕ) : Fintype.card (C4 d) = 32 * (Params.q2 d * L1 d) ^ 4 := by
  simp [C4, C3, R2, C1, Fintype.card_prod, Fintype.card_fin]

/-! ## Reciprocal-accuracy accessor (`⌈1/ε_{q,t}⌉` is exact) -/

/-- The scaffold accuracy `ε_{q,t} = (2qt)^{−C}` has an exact integer reciprocal
`1/ε_{q,t} = (2qt)^C`, so `⌈1/ε_{q,t}⌉ = (2qt)^C` with no rounding slack —
the ceiling factor of the axiom's size clause is a clean monomial. -/
theorem ceil_inv_epsQT (q t : ℕ) (hq : 0 < q) (ht : 0 < t) :
    ⌈1 / epsQT q t⌉₊ = (2 * q * t) ^ balancedFamilyConstant := by
  have hbase : (0 : ℝ) < ((2 * q * t : ℕ) : ℝ) := by
    have : 0 < 2 * q * t := by positivity
    exact_mod_cast this
  rw [epsQT, zpow_neg, zpow_natCast, one_div, inv_inv, ← Nat.cast_pow]
  exact Nat.ceil_natCast _

/-! ## Explicit monomial bounds on the balanced-family sizes -/

/-- Explicit monomial upper bound on `L₁(d) = |C₁|` from the balanced-family
citation interface's
size clause (alphabet `Fin 2`, so `|Y| = 2`; parameters `q = q₁+5`, `t = t₁`,
`ε = ε_{q₁+5,t₁}`):
`L₁(d) ≤ (q₁+7)^C · 4^{C·t₁} · ((2(q₁+5)t₁)^C)^C`.
`C = balancedFamilyConstant`. Gated on the Stage-1 balancedness side condition
`t₁ ≤ q₁+5`. -/
theorem L1_le_poly (d : ℕ) (h1 : 1 ≤ Params.t1 d)
    (h2 : Params.t1 d ≤ Params.q1 d + 5) :
    (L1 d : ℝ) ≤ ((Params.q1 d + 7 : ℕ) : ℝ) ^ balancedFamilyConstant
        * (4 : ℝ) ^ (balancedFamilyConstant * Params.t1 d)
        * (((2 * (Params.q1 d + 5) * Params.t1 d) ^ balancedFamilyConstant : ℕ) : ℝ)
            ^ balancedFamilyConstant := by
  have hq : 0 < Params.q1 d + 5 := by omega
  have hbound := (balancedFamilyData_spec (Params.q1 d + 5) (Params.t1 d) (Fin 2)
    h1 h2 (epsQT_pos hq (Params.t1_pos d)) (epsQT_lt_one hq (Params.t1_pos d))
    (by simp)).2
  have hrecip :=
    ceil_inv_epsQT (Params.q1 d + 5) (Params.t1 d) hq (Params.t1_pos d)
  rw [hrecip] at hbound
  have e1 : (Params.q1 d + 5 + 2 : ℕ) = (Params.q1 d + 7 : ℕ) := by ring
  have e2 : (Fintype.card (Fin 2) + 2 : ℕ) = 4 := by simp
  rw [e1, e2] at hbound
  convert hbound using 3

/-- Explicit monomial upper bound on `L₂(d) = |C₂|` from the balanced-family
citation interface's
size clause (alphabet `R₁ = Fin q₁ × Fin 1`, so `|Y| = q₁`; parameters
`q = q₂`, `t = t₂`, `ε = ε_{q₂,t₂}`):
`L₂(d) ≤ (q₂+2)^C · (q₁+2)^{C·t₂} · ((2·q₂·t₂)^C)^C`.
Gated on the Stage-2 balancedness side conditions `t₂ ≤ q₂`, `1 ≤ q₁`. -/
theorem L2_le_poly (d : ℕ) (h1 : 1 ≤ Params.t2 d) (h2 : Params.t2 d ≤ Params.q2 d)
    (hq1 : 1 ≤ Params.q1 d) :
    (L2 d : ℝ) ≤ ((Params.q2 d + 2 : ℕ) : ℝ) ^ balancedFamilyConstant
        * ((Params.q1 d + 2 : ℕ) : ℝ) ^ (balancedFamilyConstant * Params.t2 d)
        * (((2 * Params.q2 d * Params.t2 d) ^ balancedFamilyConstant : ℕ) : ℝ)
            ^ balancedFamilyConstant := by
  have hcard : 1 ≤ Fintype.card (Fin (Params.q1 d) × Fin 1) := by simpa using hq1
  have hbound := (balancedFamilyData_spec (Params.q2 d) (Params.t2 d)
    (Fin (Params.q1 d) × Fin 1) h1 h2
    (epsQT_pos (Params.q2_pos d) (Params.t2_pos d))
    (epsQT_lt_one (Params.q2_pos d) (Params.t2_pos d)) hcard).2
  have hrecip :=
    ceil_inv_epsQT (Params.q2 d) (Params.t2 d) (Params.q2_pos d) (Params.t2_pos d)
  rw [hrecip] at hbound
  have ecard : (Fintype.card (Fin (Params.q1 d) × Fin 1) + 2 : ℕ)
      = (Params.q1 d + 2 : ℕ) := by simp
  rw [ecard] at hbound
  convert hbound using 3

/-! ## The reduction's explicit output-size expressions -/

/-- The explicit closed-form monomial bounding the "structural" part of the
row count, `P_R(d)`: `4 · L₁-style monomial in the Stage-2 parameters`.
`|R₄| = 4·L₂(d) + n`, and `L₂(d) ≤ (q₂+2)^C·(q₁+2)^{C·t₂}·((2q₂t₂)^C)^C`, so
`P_R(d) := 4·(q₂+2)^C·(q₁+2)^{C·t₂}·((2q₂t₂)^C)^C`. Every factor is an
explicit ℕ monomial in `q₁(d), q₂(d), t₂(d)` (themselves exact functions of
`Nat.log 2 d`) with the single absolute exponent `C = balancedFamilyConstant`. -/
noncomputable def rowPoly (d : ℕ) : ℝ :=
  4 * (((Params.q2 d + 2 : ℕ) : ℝ) ^ balancedFamilyConstant
        * ((Params.q1 d + 2 : ℕ) : ℝ) ^ (balancedFamilyConstant * Params.t2 d)
        * (((2 * Params.q2 d * Params.t2 d) ^ balancedFamilyConstant : ℕ) : ℝ) ^ balancedFamilyConstant)

/-- The explicit closed-form monomial bounding the column count, `P_C(d)`:
`|C₄| = 32·(q₂(d)·L₁(d))⁴`, and `L₁(d) ≤ (q₁+7)^C·4^{C·t₁}·((2(q₁+5)t₁)^C)^C`,
so `P_C(d) := 32·(q₂ · [that monomial])⁴`. Every factor is an explicit ℕ
monomial in `q₁(d), q₂(d), t₁(d)` with the single absolute exponent
`C = balancedFamilyConstant`. -/
noncomputable def colPoly (d : ℕ) : ℝ :=
  32 * (((Params.q2 d : ℕ) : ℝ)
        * (((Params.q1 d + 7 : ℕ) : ℝ) ^ balancedFamilyConstant
            * (4 : ℝ) ^ (balancedFamilyConstant * Params.t1 d)
            * (((2 * (Params.q1 d + 5) * Params.t1 d) ^ balancedFamilyConstant : ℕ) : ℝ)
                ^ balancedFamilyConstant)) ^ 4

-- CLAIM-BEGIN lem:polytime
/-- Paper `lem:polytime`, restricted to the carrier-count statement actually
proved in Lean. The identifier is `output_size_bounds` because this theorem
does not itself certify machine constructibility or a running-time bound;
`NPCC.PolynomialSize.output_size_fixed_degree` supplies the separate
fixed-degree corollary.

For every source vector count `n` and ambient dimension `d`, under the
large-`d` balancedness gates (`t₁ ≤ q₁+5`, `t₂ ≤ q₂`, `1 ≤ q₁` — all supplied
on the normalised `d ≥ d_star` regime), the reduction's output matrix `M₄`
has row and column carriers bounded by explicit expressions:
* rows:    `|R₄| ≤ n + rowPoly d`;
* columns: `|C₄| ≤ colPoly d`.
`rowPoly` and `colPoly` are the closed forms defined above from the cited
family-size bound and the exact parameters `q₁,q₂,t₁,t₂`. Their fixed-degree
domination in the reduction's combinatorial source size is proved in
`NPCC.PolynomialSize`; serialized encodings and runtime remain separate. -/
theorem output_size_bounds (d n : ℕ)
    (ht1 : 1 ≤ Params.t1 d) (ht1q : Params.t1 d ≤ Params.q1 d + 5)
    (ht2 : 1 ≤ Params.t2 d) (ht2q : Params.t2 d ≤ Params.q2 d)
    (hq1 : 1 ≤ Params.q1 d) :
    (Fintype.card (R4 d n) : ℝ) ≤ (n : ℝ) + rowPoly d
      ∧ (Fintype.card (C4 d) : ℝ) ≤ colPoly d := by
  refine ⟨?_, ?_⟩
  · -- rows: |R₄| = 4·L₂(d) + n ≤ n + 4·(L₂ monomial) = n + rowPoly d.
    rw [card_R4, rowPoly]
    have hL2 := L2_le_poly d ht2 ht2q hq1
    have hcast : ((4 * L2 d + n : ℕ) : ℝ) = (n : ℝ) + 4 * (L2 d : ℝ) := by
      push_cast; ring
    rw [hcast]
    have : 4 * (L2 d : ℝ)
        ≤ 4 * (((Params.q2 d + 2 : ℕ) : ℝ) ^ balancedFamilyConstant
              * ((Params.q1 d + 2 : ℕ) : ℝ) ^ (balancedFamilyConstant * Params.t2 d)
              * (((2 * Params.q2 d * Params.t2 d) ^ balancedFamilyConstant : ℕ) : ℝ)
                  ^ balancedFamilyConstant) := by
      gcongr
    linarith
  · -- columns: |C₄| = 32·(q₂·L₁)⁴ ≤ 32·(q₂·(L₁ monomial))⁴ = colPoly d.
    rw [card_C4, colPoly]
    have hL1 := L1_le_poly d ht1 ht1q
    have hcast : ((32 * (Params.q2 d * L1 d) ^ 4 : ℕ) : ℝ)
        = 32 * ((Params.q2 d : ℝ) * (L1 d : ℝ)) ^ 4 := by
      push_cast; ring
    rw [hcast]
    have hq2nn : (0 : ℝ) ≤ (Params.q2 d : ℝ) := by positivity
    gcongr
-- CLAIM-END lem:polytime

/-! ## Corollary: `|R₄|` is linear in `n` with a `d`-only slope-1 form -/

/-- Companion (wrapper convenience): the row bound in the exact "linear in `n`,
plus a `d`-only constant" shape the Layer-B reduction records. Needs ONLY the
Stage-2 gates (`|R₄|` is independent of the Stage-1 family). -/
theorem card_R4_le (d n : ℕ)
    (ht2 : 1 ≤ Params.t2 d) (ht2q : Params.t2 d ≤ Params.q2 d)
    (hq1 : 1 ≤ Params.q1 d) :
    (Fintype.card (R4 d n) : ℝ) ≤ (n : ℝ) + rowPoly d := by
  rw [card_R4, rowPoly]
  have hL2 := L2_le_poly d ht2 ht2q hq1
  have hcast : ((4 * L2 d + n : ℕ) : ℝ) = (n : ℝ) + 4 * (L2 d : ℝ) := by
    push_cast; ring
  rw [hcast]
  have : 4 * (L2 d : ℝ)
      ≤ 4 * (((Params.q2 d + 2 : ℕ) : ℝ) ^ balancedFamilyConstant
            * ((Params.q1 d + 2 : ℕ) : ℝ) ^ (balancedFamilyConstant * Params.t2 d)
            * (((2 * Params.q2 d * Params.t2 d) ^ balancedFamilyConstant : ℕ) : ℝ)
                ^ balancedFamilyConstant) := by
    gcongr
  linarith

end NPCC
