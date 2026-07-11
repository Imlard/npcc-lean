import Mathlib
import NPCC.Size
import NPCC.GateDischarge

/-!
# Fixed-degree output-size bounds

`NPCC.Size` bounds the two carriers by the explicit expressions `rowPoly` and
`colPoly`.  This module proves the missing asymptotic step: on the normalized
power-of-two regime used by the reduction, both expressions are bounded by a
power of the normalized dimension whose exponent is one absolute constant.

The only nontrivial cancellation is the Stage-2 factor
`(q1 + 2) ^ (C * t2)`.  Writing `d = 2^k` and `ell = log_2 k`, the definitions
give `log_2 (q1 + 2) <= 2*ell + 3` and `t2 <= 2*ceil(3*k/ell)`, hence
`log_2 (q1 + 2) * t2 <= 24*k`.  Therefore that apparently variable-exponent
factor is at most `d^(24*C)`.
-/

namespace NPCC

open Workspace.Types.Interlace

/-- A fixed exponent for the row-size expression. -/
noncomputable def fixedRowDegree : Nat :=
  2 + 26 * balancedFamilyConstant + 3 * balancedFamilyConstant * balancedFamilyConstant

/-- A fixed exponent for the column-size expression. -/
noncomputable def fixedColumnDegree : Nat :=
  5 + 4 * (1 + 257 * balancedFamilyConstant +
    3 * balancedFamilyConstant * balancedFamilyConstant)

/-- One fixed exponent that dominates both carrier-size expressions. -/
noncomputable def fixedStructuralDegree : Nat :=
  max fixedRowDegree fixedColumnDegree

theorem fixedStructuralDegree_pos : 0 < fixedStructuralDegree := by
  unfold fixedStructuralDegree fixedRowDegree
  omega

/-- A coarse linear-vs-exponential estimate used for `t1`. -/
private theorem one_twenty_eight_mul_le_two_pow {k : Nat} (hk : 16 <= k) :
    128 * k <= 2 ^ k := by
  induction k with
  | zero => omega
  | succ n ih =>
      by_cases hn : n < 16
      · have hn15 : n = 15 := by omega
        subst hn15
        norm_num
      · have hn16 : 16 <= n := by omega
        have hih := ih hn16
        have h128 : 128 <= 2 ^ n := by
          calc
            128 = 2 ^ 7 := by norm_num
            _ <= 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [pow_succ]
        omega

/-- The polylogarithmic `q1` carrier is below `2^k` in the reduction regime. -/
private theorem four_sq_add_five_le_two_pow {k : Nat} (hk : 16 <= k) :
    4 * k ^ 2 + 5 <= 2 ^ k := by
  induction k with
  | zero => omega
  | succ n ih =>
      by_cases hn : n < 16
      · have hn15 : n = 15 := by omega
        subst hn15
        norm_num
      · have hn16 : 16 <= n := by omega
        have hih := ih hn16
        have hstep : 4 * (n + 1) ^ 2 + 5 <= 2 * (4 * n ^ 2 + 5) := by
          nlinarith
        have hdouble := Nat.mul_le_mul_left 2 hih
        simpa [Nat.succ_eq_add_one, pow_succ, Nat.mul_comm] using le_trans hstep hdouble

/-- The load-bearing Stage-2 cancellation:
`log2(q1+2) * t2 <= 24 * log2(d)` when `d = 2^k` is in the constructor regime. -/
theorem a_mul_t2_le_twenty_four_log {k : Nat} (hk : 2 ^ 18 <= k) :
    Params.a (2 ^ k) * Params.t2 (2 ^ k) <= 24 * k := by
  let ell := Nat.log 2 k
  let u := (3 * k + ell - 1) / ell
  have hell18 : 18 <= ell := by
    rw [show ell = Nat.log 2 k by rfl]
    have hmono := Nat.log_mono_right (b := 2) hk
    simpa [log_two_pow] using hmono
  have hell_pos : 1 <= ell := by omega
  have hell_le_k : ell <= k := by
    exact Nat.log_le_self 2 k
  have ha : Params.a (2 ^ k) <= 2 * ell + 3 := by
    have hpow : IsPow2 (2 ^ k) := ⟨k, rfl⟩
    have hlog256 : 256 <= Nat.log 2 (2 ^ k) := by
      simp only [log_two_pow]
      omega
    simpa [ell, log_two_pow] using
      gate_a_le_two_loglog_add_three (2 ^ k) hpow hlog256
  have ha3 : Params.a (2 ^ k) <= 3 * ell := by omega
  have hu_pos : 1 <= u := by
    have hnum : ell <= 3 * k + ell - 1 := by omega
    have : 1 <= (3 * k + ell - 1) / ell := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      simpa using hnum
    exact this
  have ht2 : Params.t2 (2 ^ k) <= 2 * u := by
    unfold Params.t2
    simp only [log_two_pow]
    exact ceilPowTwo_le_two_mul hu_pos
  have hu_mul : u * ell <= 3 * k + ell - 1 := by
    exact Nat.div_mul_le_self _ _
  calc
    Params.a (2 ^ k) * Params.t2 (2 ^ k) <= (3 * ell) * (2 * u) :=
      Nat.mul_le_mul ha3 ht2
    _ = 6 * (u * ell) := by ring
    _ <= 6 * (3 * k + ell - 1) := Nat.mul_le_mul_left 6 hu_mul
    _ <= 24 * k := by omega

/-- Coarse parameter bounds sufficient for fixed-degree size domination. -/
private theorem normalized_parameter_bounds {k : Nat} (hk : 2 ^ 18 <= k) :
    Params.q1 (2 ^ k) + 7 <= 2 ^ k /\
      Params.t1 (2 ^ k) <= 2 ^ k /\
      Params.q2 (2 ^ k) = 2 ^ k /\
      Params.t2 (2 ^ k) <= 2 ^ k := by
  have hk16 : 16 <= k := by omega
  have hk1 : 1 <= k := by omega
  have hq1 : Params.q1 (2 ^ k) + 7 <= 2 ^ k := by
    have hq := Params.q1_add_two_le (d := 2 ^ k) (by simpa [log_two_pow] using hk1)
    rw [log_two_pow] at hq
    exact le_trans (by omega) (four_sq_add_five_le_two_pow hk16)
  have ht1 : Params.t1 (2 ^ k) <= 2 ^ k := by
    have ht := (Params.t1_bracket (d := 2 ^ k) (by simpa [log_two_pow] using hk1)).2
    rw [log_two_pow] at ht
    exact le_trans ht (one_twenty_eight_mul_le_two_pow hk16)
  have hq2 : Params.q2 (2 ^ k) = 2 ^ k := Params.q2_eq_self rfl
  have ht2 : Params.t2 (2 ^ k) <= 2 ^ k := by
    have hell : 1 <= Nat.log 2 (Nat.log 2 (2 ^ k)) := by
      simp only [log_two_pow]
      have : 18 <= Nat.log 2 k := by
        have hmono := Nat.log_mono_right (b := 2) hk
        simpa [log_two_pow] using hmono
      omega
    have ht := Params.t2_le hell
    rw [log_two_pow] at ht
    exact le_trans ht (six_mul_le_two_pow (by omega))
  exact ⟨hq1, ht1, hq2, ht2⟩

/-! ## Natural-valued forms of the explicit size expressions -/

/-- The natural-valued expression whose real cast is `rowPoly`. -/
noncomputable def rowPolyNat (d : Nat) : Nat :=
  4 * ((Params.q2 d + 2) ^ balancedFamilyConstant
        * (Params.q1 d + 2) ^ (balancedFamilyConstant * Params.t2 d)
        * ((2 * Params.q2 d * Params.t2 d) ^ balancedFamilyConstant) ^
            balancedFamilyConstant)

/-- The natural-valued expression whose real cast is `colPoly`. -/
noncomputable def colPolyNat (d : Nat) : Nat :=
  32 * (Params.q2 d
        * ((Params.q1 d + 7) ^ balancedFamilyConstant
            * 4 ^ (balancedFamilyConstant * Params.t1 d)
            * ((2 * (Params.q1 d + 5) * Params.t1 d) ^ balancedFamilyConstant) ^
                balancedFamilyConstant)) ^ 4

theorem rowPoly_eq_natCast (d : Nat) : rowPoly d = (rowPolyNat d : Real) := by
  simp [rowPoly, rowPolyNat, Nat.cast_mul, Nat.cast_pow]

theorem colPoly_eq_natCast (d : Nat) : colPoly d = (colPolyNat d : Real) := by
  simp [colPoly, colPolyNat, Nat.cast_mul, Nat.cast_pow]

private theorem q1_variable_power_le {k : Nat} (hk : 2 ^ 18 <= k) :
    (Params.q1 (2 ^ k) + 2) ^
        (balancedFamilyConstant * Params.t2 (2 ^ k))
      <= (2 ^ k) ^ (24 * balancedFamilyConstant) := by
  have hcancel := a_mul_t2_le_twenty_four_log hk
  have hexp :
      Params.a (2 ^ k) *
          (balancedFamilyConstant * Params.t2 (2 ^ k))
        <= k * (24 * balancedFamilyConstant) := by
    calc
      Params.a (2 ^ k) *
            (balancedFamilyConstant * Params.t2 (2 ^ k))
          = balancedFamilyConstant *
              (Params.a (2 ^ k) * Params.t2 (2 ^ k)) := by ring
      _ <= balancedFamilyConstant * (24 * k) :=
        Nat.mul_le_mul_left balancedFamilyConstant hcancel
      _ = k * (24 * balancedFamilyConstant) := by ring
  have hp := Nat.pow_le_pow_right (by norm_num : 1 <= (2 : Nat)) hexp
  have hlog : 1 <= Nat.log 2 (2 ^ k) := by simp; omega
  rw [Params.q1_add_two_pow hlog]
  simpa only [pow_mul] using hp

private theorem four_t1_power_le {k : Nat} (hk : 2 ^ 18 <= k) :
    4 ^ (balancedFamilyConstant * Params.t1 (2 ^ k))
      <= (2 ^ k) ^ (256 * balancedFamilyConstant) := by
  have ht1 := (normalized_parameter_bounds hk).2.1
  have ht1linear : Params.t1 (2 ^ k) <= 128 * k := by
    have hk1 : 1 <= k := by omega
    have ht := (Params.t1_bracket (d := 2 ^ k)
      (by simpa [log_two_pow] using hk1)).2
    simpa [log_two_pow] using ht
  have hexp :
      2 * (balancedFamilyConstant * Params.t1 (2 ^ k))
        <= k * (256 * balancedFamilyConstant) := by
    calc
      2 * (balancedFamilyConstant * Params.t1 (2 ^ k))
          = (2 * balancedFamilyConstant) * Params.t1 (2 ^ k) := by ring
      _ <= (2 * balancedFamilyConstant) * (128 * k) :=
        Nat.mul_le_mul_left (2 * balancedFamilyConstant) ht1linear
      _ = k * (256 * balancedFamilyConstant) := by ring
  have hp := Nat.pow_le_pow_right (by norm_num : 1 <= (2 : Nat)) hexp
  simpa only [show (4 : Nat) = 2 ^ 2 by norm_num, pow_mul] using hp

private theorem row_reciprocal_factor_le {k : Nat} (hk : 2 ^ 18 <= k) :
    ((2 * Params.q2 (2 ^ k) * Params.t2 (2 ^ k)) ^ balancedFamilyConstant) ^
        balancedFamilyConstant
      <= (2 ^ k) ^ (3 * balancedFamilyConstant * balancedFamilyConstant) := by
  obtain ⟨_, _, hq2, ht2⟩ := normalized_parameter_bounds hk
  have hd2 : 2 <= 2 ^ k := by
    have : 1 <= k := by omega
    calc
      2 = 2 ^ 1 := by norm_num
      _ <= 2 ^ k := Nat.pow_le_pow_right (by norm_num) this
  have hbase :
      2 * Params.q2 (2 ^ k) * Params.t2 (2 ^ k) <= (2 ^ k) ^ 3 := by
    rw [hq2]
    calc
      2 * 2 ^ k * Params.t2 (2 ^ k) <= 2 * 2 ^ k * 2 ^ k :=
        Nat.mul_le_mul_left (2 * 2 ^ k) ht2
      _ <= 2 ^ k * 2 ^ k * 2 ^ k := by nlinarith
      _ = (2 ^ k) ^ 3 := by ring
  have h1 := Nat.pow_le_pow_left hbase balancedFamilyConstant
  have h2 := Nat.pow_le_pow_left h1 balancedFamilyConstant
  simpa only [pow_mul] using h2

private theorem column_reciprocal_factor_le {k : Nat} (hk : 2 ^ 18 <= k) :
    ((2 * (Params.q1 (2 ^ k) + 5) * Params.t1 (2 ^ k)) ^
        balancedFamilyConstant) ^ balancedFamilyConstant
      <= (2 ^ k) ^ (3 * balancedFamilyConstant * balancedFamilyConstant) := by
  obtain ⟨hq1, ht1, _, _⟩ := normalized_parameter_bounds hk
  have hd2 : 2 <= 2 ^ k := by
    have : 1 <= k := by omega
    calc
      2 = 2 ^ 1 := by norm_num
      _ <= 2 ^ k := Nat.pow_le_pow_right (by norm_num) this
  have hq1' : Params.q1 (2 ^ k) + 5 <= 2 ^ k := by omega
  have hbase :
      2 * (Params.q1 (2 ^ k) + 5) * Params.t1 (2 ^ k) <= (2 ^ k) ^ 3 := by
    calc
      2 * (Params.q1 (2 ^ k) + 5) * Params.t1 (2 ^ k)
          <= 2 * (2 ^ k) * (2 ^ k) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hq1') ht1
      _ <= 2 ^ k * 2 ^ k * 2 ^ k := by nlinarith
      _ = (2 ^ k) ^ 3 := by ring
  have h1 := Nat.pow_le_pow_left hbase balancedFamilyConstant
  have h2 := Nat.pow_le_pow_left h1 balancedFamilyConstant
  simpa only [pow_mul] using h2

/-! ## Fixed powers of the normalized dimension -/

theorem rowPolyNat_le_fixed_power {k : Nat} (hk : 2 ^ 18 <= k) :
    rowPolyNat (2 ^ k) <= (2 ^ k) ^ fixedRowDegree := by
  obtain ⟨_, _, hq2, _⟩ := normalized_parameter_bounds hk
  have hk1 : 1 <= k := by omega
  have hd2 : 2 <= 2 ^ k := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ <= 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
  have hfour : 4 <= (2 ^ k) ^ 2 := by
    have h := Nat.pow_le_pow_left hd2 2
    norm_num at h ⊢
    exact h
  have hqbase : Params.q2 (2 ^ k) + 2 <= (2 ^ k) ^ 2 := by
    rw [hq2]
    nlinarith
  have hqfactor := Nat.pow_le_pow_left hqbase balancedFamilyConstant
  have hqfactor' :
      (Params.q2 (2 ^ k) + 2) ^ balancedFamilyConstant
        <= (2 ^ k) ^ (2 * balancedFamilyConstant) := by
    simpa only [pow_mul] using hqfactor
  have hvariable := q1_variable_power_le hk
  have hreciprocal := row_reciprocal_factor_le hk
  unfold rowPolyNat
  calc
    4 * ((Params.q2 (2 ^ k) + 2) ^ balancedFamilyConstant
          * (Params.q1 (2 ^ k) + 2) ^
              (balancedFamilyConstant * Params.t2 (2 ^ k))
          * ((2 * Params.q2 (2 ^ k) * Params.t2 (2 ^ k)) ^
              balancedFamilyConstant) ^ balancedFamilyConstant)
        <= (2 ^ k) ^ 2 *
          ((2 ^ k) ^ (2 * balancedFamilyConstant)
            * (2 ^ k) ^ (24 * balancedFamilyConstant)
            * (2 ^ k) ^
                (3 * balancedFamilyConstant * balancedFamilyConstant)) := by
      exact Nat.mul_le_mul hfour
        (Nat.mul_le_mul (Nat.mul_le_mul hqfactor' hvariable) hreciprocal)
    _ = (2 ^ k) ^ fixedRowDegree := by
      simp only [fixedRowDegree, pow_add]
      ring

theorem colPolyNat_le_fixed_power {k : Nat} (hk : 2 ^ 18 <= k) :
    colPolyNat (2 ^ k) <= (2 ^ k) ^ fixedColumnDegree := by
  obtain ⟨hq1, _, hq2, _⟩ := normalized_parameter_bounds hk
  have hk1 : 1 <= k := by omega
  have hd2 : 2 <= 2 ^ k := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ <= 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
  have h32 : 32 <= (2 ^ k) ^ 5 := by
    have := Nat.pow_le_pow_left hd2 5
    norm_num at this ⊢
    exact this
  have hq1factor := Nat.pow_le_pow_left hq1 balancedFamilyConstant
  have ht1factor := four_t1_power_le hk
  have hreciprocal := column_reciprocal_factor_le hk
  have hinside :
      Params.q2 (2 ^ k) *
          ((Params.q1 (2 ^ k) + 7) ^ balancedFamilyConstant
            * 4 ^ (balancedFamilyConstant * Params.t1 (2 ^ k))
            * ((2 * (Params.q1 (2 ^ k) + 5) * Params.t1 (2 ^ k)) ^
                balancedFamilyConstant) ^ balancedFamilyConstant)
        <= (2 ^ k) ^ 1 *
          ((2 ^ k) ^ balancedFamilyConstant
            * (2 ^ k) ^ (256 * balancedFamilyConstant)
            * (2 ^ k) ^
                (3 * balancedFamilyConstant * balancedFamilyConstant)) := by
    have hq2' : Params.q2 (2 ^ k) <= (2 ^ k) ^ 1 := by simp [hq2]
    exact Nat.mul_le_mul hq2'
      (Nat.mul_le_mul (Nat.mul_le_mul hq1factor ht1factor) hreciprocal)
  have hfourth := Nat.pow_le_pow_left hinside 4
  unfold colPolyNat
  calc
    32 * (Params.q2 (2 ^ k) *
          ((Params.q1 (2 ^ k) + 7) ^ balancedFamilyConstant
            * 4 ^ (balancedFamilyConstant * Params.t1 (2 ^ k))
            * ((2 * (Params.q1 (2 ^ k) + 5) * Params.t1 (2 ^ k)) ^
                balancedFamilyConstant) ^ balancedFamilyConstant)) ^ 4
        <= (2 ^ k) ^ 5 *
          ((2 ^ k) ^ 1 *
            ((2 ^ k) ^ balancedFamilyConstant
              * (2 ^ k) ^ (256 * balancedFamilyConstant)
              * (2 ^ k) ^
                  (3 * balancedFamilyConstant * balancedFamilyConstant))) ^ 4 := by
      exact Nat.mul_le_mul h32 hfourth
    _ = (2 ^ k) ^ fixedColumnDegree := by
      simp only [fixedColumnDegree, pow_add, pow_mul]
      ring

theorem rowPoly_le_fixed_power {k : Nat} (hk : 2 ^ 18 <= k) :
    rowPoly (2 ^ k) <= ((2 ^ k : Nat) : Real) ^ fixedStructuralDegree := by
  rw [rowPoly_eq_natCast]
  have h := rowPolyNat_le_fixed_power hk
  have hdegree : fixedRowDegree <= fixedStructuralDegree := le_max_left _ _
  have hp : (2 ^ k) ^ fixedRowDegree <= (2 ^ k) ^ fixedStructuralDegree :=
    Nat.pow_le_pow_right (by positivity) hdegree
  exact_mod_cast le_trans h hp

theorem colPoly_le_fixed_power {k : Nat} (hk : 2 ^ 18 <= k) :
    colPoly (2 ^ k) <= ((2 ^ k : Nat) : Real) ^ fixedStructuralDegree := by
  rw [colPoly_eq_natCast]
  have h := colPolyNat_le_fixed_power hk
  have hdegree : fixedColumnDegree <= fixedStructuralDegree := le_max_right _ _
  have hp : (2 ^ k) ^ fixedColumnDegree <= (2 ^ k) ^ fixedStructuralDegree :=
    Nat.pow_le_pow_right (by positivity) hdegree
  exact_mod_cast le_trans h hp

/-- The explicit carrier bounds are dominated by one fixed power of the
normalized dimension.  This is the kernel-level fixed-degree asymptotic
corollary missing from `output_size_bounds`. -/
theorem output_size_fixed_degree {d n : Nat}
    (hpow : IsPow2 d) (hlog : 2 ^ 18 <= Nat.log 2 d) (hchk : Checklist d) :
    Fintype.card (R4 d n) <= n + d ^ fixedStructuralDegree /\
      Fintype.card (C4 d) <= d ^ fixedStructuralDegree := by
  rcases hpow with ⟨k, rfl⟩
  rw [log_two_pow] at hlog
  have hsize := output_size_bounds (2 ^ k) n
    (Params.t1_pos (2 ^ k)) hchk.t1_le_q1_add_five
    (Params.t2_pos (2 ^ k)) hchk.t2_le_q2 hchk.one_le_q1
  have hrow := rowPoly_le_fixed_power hlog
  have hcol := colPoly_le_fixed_power hlog
  constructor
  · have hreal :
        (Fintype.card (R4 (2 ^ k) n) : Real)
          <= (n : Real) + ((2 ^ k : Nat) : Real) ^ fixedStructuralDegree :=
      le_trans hsize.1 (by gcongr)
    exact_mod_cast hreal
  · have hreal :
        (Fintype.card (C4 (2 ^ k)) : Real)
          <= ((2 ^ k : Nat) : Real) ^ fixedStructuralDegree :=
      le_trans hsize.2 hcol
    exact_mod_cast hreal

end NPCC
