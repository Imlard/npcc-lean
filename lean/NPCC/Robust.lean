import Mathlib
import NPCC.Complexity
import Workspace.Types.Interlace

/-! # Robustness (paper def:robust), typed form. -/

namespace NPCC

open Workspace.Types.CommComplexity Workspace.Types.Interlace

-- CLAIM-BEGIN def:robust
/-- Paper `def:robust` ((δ,b)-robust matrix), typed form over the complexity
layer. `comp M` is `D f`; the paper's one-copy bracket `⟨M,1,x,y⟩` is the
`p = 1` family `bracketGE X Y 1 x y` under the ambient game
`interlaceFun f 1`, with row density `x = 2^(-b)` (real exponent, `b ≥ 0` at
use sites) and the three column densities `1/2+δ`, `1/8+δ/4`, `1/4+δ/2` of
conditions R2–R4. R1 is `1 ≤ D f`. R3/R4 compare in `ℤ` — the paper's
`comp M − 2` and `comp M − 1` are integer statements and `ℕ`-truncation would
silently strengthen them at small `D f`. The side condition `δ ∈ (0, 1/2)`
is a use-site hypothesis per house convention. -/
def IsRobust {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (δ b : ℝ) : Prop :=
  1 ≤ D f ∧
  D f ≤ Dfamily (interlaceFun f 1)
      (bracketGE X Y 1 ((2 : ℝ) ^ (-b)) (1 / 2 + δ)) ∧
  (D f : ℤ) - 2 ≤ (Dfamily (interlaceFun f 1)
      (bracketGE X Y 1 ((2 : ℝ) ^ (-b)) (1 / 8 + δ / 4)) : ℤ) ∧
  (D f : ℤ) - 1 ≤ (Dfamily (interlaceFun f 1)
      (bracketGE X Y 1 ((2 : ℝ) ^ (-b)) (1 / 4 + δ / 2)) : ℤ)
-- CLAIM-END def:robust

end NPCC
