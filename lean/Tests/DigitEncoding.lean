import Mathlib
import Workspace.Types.Interlace

/-! Isolated regression test for base-`n` tuple encoding. The production
formalization uses the corresponding declarations in `NPCC.Twin`; these names
live under `Workspace.Tests` so the test can be imported without collisions. -/

namespace Workspace.Tests
open Workspace.Types.Interlace

def encCol {p n : ℕ} (c : Fin p → Fin n) : ℕ :=
  ∑ γ : Fin p, (c γ : ℕ) * n ^ (γ : ℕ)

theorem encCol_succ {p n : ℕ} (c : Fin (p + 1) → Fin n) :
    encCol c = (c 0 : ℕ) + n * encCol (fun γ : Fin p => c γ.succ) := by
  unfold encCol
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro γ _
  ring

theorem encCol_digit {p n : ℕ} (hn : 0 < n) (c : Fin p → Fin n) :
    encCol c < n ^ p ∧
    ∀ q : Fin p, (encCol c / n ^ (q : ℕ)) % n = (c q : ℕ) := by
  induction p with
  | zero =>
    constructor
    · simp [encCol]
    · intro q; exact absurd q.isLt (Nat.not_lt_zero _)
  | succ p ih =>
    have hc0 : (c 0 : ℕ) < n := (c 0).isLt
    set tail : Fin p → Fin n := fun γ => c γ.succ with htail
    obtain ⟨ihlt, ihdig⟩ := ih tail
    have hrec : encCol c = (c 0 : ℕ) + n * encCol tail := encCol_succ c
    constructor
    · rw [hrec]
      have : n * encCol tail + n ≤ n ^ (p+1) := by
        have : encCol tail + 1 ≤ n ^ p := ihlt
        calc n * encCol tail + n = n * (encCol tail + 1) := by ring
          _ ≤ n * n ^ p := by exact Nat.mul_le_mul_left n this
          _ = n ^ (p+1) := by rw [pow_succ]; ring
      omega
    · intro q
      refine Fin.cases ?_ ?_ q
      · simp only [Fin.val_zero, pow_zero, Nat.div_one]
        rw [hrec, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc0]
      · intro q'
        simp only [Fin.val_succ, pow_succ]
        rw [hrec]
        rw [mul_comm (n ^ (q' : ℕ)) n, ← Nat.div_div_eq_div_mul]
        rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hc0, Nat.zero_add]
        exact ihdig q'

end Workspace.Tests

namespace Workspace.Tests
theorem encCol_injective {p n : ℕ} (hn : 0 < n) :
    Function.Injective (encCol (p := p) (n := n)) := by
  intro c d hcd
  funext q
  apply Fin.ext
  have h1 := (encCol_digit hn c).2 q
  have h2 := (encCol_digit hn d).2 q
  rw [hcd] at h1
  rw [h1] at h2
  exact h2
end Workspace.Tests
