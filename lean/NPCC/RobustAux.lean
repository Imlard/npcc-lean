import Mathlib
import NPCC.Robust

namespace NPCC

open Workspace.Types.CommComplexity Workspace.Types.Interlace

-- CLAIM-BEGIN aux:robust-accessors
/-- Accessor extracting the R2 conjunct (the `p = 1` bracket comparison at
column density `1/2 + δ`) from an `IsRobust` witness. -/
theorem IsRobust.r2 {X Y : Type*} [Fintype X] [Fintype Y] {f : X → Y → Bool} {δ b : ℝ}
    (h : IsRobust f δ b) :
    D f ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 ((2 : ℝ) ^ (-b)) (1 / 2 + δ)) :=
-- CLAIM-END aux:robust-accessors
  h.2.1

/-- Accessor extracting the R1 conjunct (`1 ≤ D f`) from an `IsRobust` witness. -/
theorem IsRobust.r1 {X Y : Type*} [Fintype X] [Fintype Y] {f : X → Y → Bool} {δ b : ℝ}
    (h : IsRobust f δ b) :
    1 ≤ D f :=
  h.1

/-- Accessor extracting the R3 conjunct (the integer comparison `D f - 2 ≤ …`
at column density `1/8 + δ/4`) from an `IsRobust` witness. -/
theorem IsRobust.r3 {X Y : Type*} [Fintype X] [Fintype Y] {f : X → Y → Bool} {δ b : ℝ}
    (h : IsRobust f δ b) :
    (D f : ℤ) - 2 ≤ (Dfamily (interlaceFun f 1)
        (bracketGE X Y 1 ((2 : ℝ) ^ (-b)) (1 / 8 + δ / 4)) : ℤ) :=
  h.2.2.1

/-- Accessor extracting the R4 conjunct (the integer comparison `D f - 1 ≤ …`
at column density `1/4 + δ/2`) from an `IsRobust` witness. -/
theorem IsRobust.r4 {X Y : Type*} [Fintype X] [Fintype Y] {f : X → Y → Bool} {δ b : ℝ}
    (h : IsRobust f δ b) :
    (D f : ℤ) - 1 ≤ (Dfamily (interlaceFun f 1)
        (bracketGE X Y 1 ((2 : ℝ) ^ (-b)) (1 / 4 + δ / 2)) : ℤ) :=
  h.2.2.2

end NPCC
