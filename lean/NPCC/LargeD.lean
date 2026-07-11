import Mathlib
import NPCC.VBP
import NPCC.Scaffold

/-! # The large-parameter checklist and `d_star`

Appendix C repeatedly assumes that the power-of-two dimension `d` is large
enough for a common collection of arithmetic inequalities. `Checklist d`
bundles those exact gates: strict density bounds, the divisibility identities
`q1+2 = r1*t1` and `q2 = r2*t2`, hard-seed thresholds, logarithm identities,
and every endpoint inequality used by the stage proofs.

The theorem `large_d_checklist` proves
`∃ d₀, ∀ d, IsPow2 d → d₀ ≤ d → Checklist d`; only then does `d_star` select
one such threshold by classical choice. The witness is an explicit large power
of two. Discrete parameters are evaluated at `k := Nat.log 2 d` with
`d = 2 ^ k`, and real densities have the form `(2 : ℝ) ^ (-(·))`. -/

namespace NPCC

open scoped BigOperators

/-! ## Power-of-two predicate and the reduction to the exponent `k` -/

/-- `d` is a power of two. Working predicate for the checklist domain (the
normaliser guarantees the ambient dimension is a power of two). -/
def IsPow2 (d : ℕ) : Prop := ∃ k, d = 2 ^ k

theorem IsPow2.pos {d : ℕ} (h : IsPow2 d) : 0 < d := by
  obtain ⟨k, rfl⟩ := h; positivity

/-- For a power of two `d = 2 ^ k`, `Nat.log 2 d = k`. -/
theorem log_two_pow (k : ℕ) : Nat.log 2 (2 ^ k) = k :=
  Nat.log_pow (by norm_num) k

/-! ## `ceilPowTwo` two-sided bracket -/

/-- `ceilPowTwo z ≤ 2 z` for `z ≥ 1` (the Deep-Think up-to-2× inflation
warning, made a proved bound). Together with `le_ceilPowTwo` this brackets
`ceilPowTwo z ∈ [z, 2z]`. -/
theorem ceilPowTwo_le_two_mul {z : ℕ} (hz : 1 ≤ z) : ceilPowTwo z ≤ 2 * z := by
  unfold ceilPowTwo
  rcases Nat.eq_or_lt_of_le hz with h | h
  · simp [← h]
  · have hcpos : 0 < Nat.clog 2 z := Nat.clog_pos (by norm_num) h
    have key : 2 ^ (Nat.clog 2 z - 1) < z :=
      Nat.pow_pred_clog_lt_self (by norm_num) h
    calc 2 ^ Nat.clog 2 z = 2 * 2 ^ (Nat.clog 2 z - 1) := by
              rw [← pow_succ']; congr 1; omega
      _ ≤ 2 * z := by omega

/-- `ceilPowTwo` is a power of two, with its exact exponent. -/
theorem ceilPowTwo_eq_pow (z : ℕ) : ceilPowTwo z = 2 ^ Nat.clog 2 z := rfl

/-- Monotonicity of `ceilPowTwo`. -/
theorem ceilPowTwo_mono {z w : ℕ} (h : z ≤ w) : ceilPowTwo z ≤ ceilPowTwo w :=
  Nat.pow_le_pow_right (by norm_num) (Nat.clog_mono_right 2 h)

/-- A power of two divides another iff it is `≤` it: for exponents,
`2 ^ i ∣ 2 ^ j ↔ 2 ^ i ≤ 2 ^ j`. Consumed by the exact divisibility facts. -/
theorem pow_two_dvd_of_le {i j : ℕ} (h : (2 : ℕ) ^ i ≤ 2 ^ j) :
    (2 : ℕ) ^ i ∣ 2 ^ j :=
  pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by norm_num)).mp h)

/-- `a + b − 1 ≤ a·b` for `a, b ≥ 1` (i.e. `(a−1)(b−1) ≥ 0`); the arithmetic
core behind the ceiling-division upper bound. -/
theorem addsub_le_mul {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : a + b - 1 ≤ a * b := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hb
  ring_nf; omega

/-- Ceiling division is at most the dividend: `⌈a/b⌉ = (a+b−1)/b ≤ a` for
`b ≥ 1`. -/
theorem ceilDiv_le {a b : ℕ} (hb : 1 ≤ b) : (a + b - 1) / b ≤ a := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; rw [Nat.zero_add, Nat.div_eq_of_lt (by omega)]
  · have h2 : (a + b - 1)/b ≤ (a * b)/b :=
      Nat.div_le_div_right (addsub_le_mul ha hb)
    rwa [Nat.mul_div_cancel _ (by omega)] at h2

/-! ## Discrete parameter bounds at `d = 2 ^ k` (`k := Nat.log 2 d`)

Every parameter is bracketed by its `ceilPowTwo` two-sided bound; the point of
the section is to reduce every discrete side condition to a monotone
polynomial-in-`k` inequality that holds for all `k ≥ K₀`. -/

namespace Params

open NPCC

variable {d : ℕ}

/-- `q₁ + 2 = ceilPowTwo (2 (log d)²)` (unfolds the ℕ-truncation once
`2 (log d)² ≥ 1`, so `ceilPowTwo … ≥ 2`). -/
theorem q1_add_two (hlog : 1 ≤ Nat.log 2 d) :
    q1 d + 2 = ceilPowTwo (2 * Nat.log 2 d ^ 2) := by
  have h2 : 2 ≤ 2 * Nat.log 2 d ^ 2 := by nlinarith
  have hle : 2 ≤ ceilPowTwo (2 * Nat.log 2 d ^ 2) :=
    le_trans h2 (le_ceilPowTwo _)
  unfold q1
  omega

/-- `q₁ + 2` is a power of two: `= 2 ^ a d`. -/
theorem q1_add_two_pow (hlog : 1 ≤ Nat.log 2 d) :
    q1 d + 2 = 2 ^ a d := by
  rw [q1_add_two hlog]; rfl

/-- `2 (log d)² ≤ q₁ + 2` (lower bracket). -/
theorem le_q1_add_two (hlog : 1 ≤ Nat.log 2 d) :
    2 * Nat.log 2 d ^ 2 ≤ q1 d + 2 := by
  rw [q1_add_two hlog]; exact le_ceilPowTwo _

/-- `q₁ + 2 ≤ 4 (log d)²` (upper bracket via `ceilPowTwo ≤ 2·`). -/
theorem q1_add_two_le (hlog : 1 ≤ Nat.log 2 d) :
    q1 d + 2 ≤ 4 * Nat.log 2 d ^ 2 := by
  rw [q1_add_two hlog]
  have : ceilPowTwo (2 * Nat.log 2 d ^ 2) ≤ 2 * (2 * Nat.log 2 d ^ 2) :=
    ceilPowTwo_le_two_mul (by nlinarith)
  omega

/-- `64 log d ≤ t₁ ≤ 128 log d` (two-sided bracket). -/
theorem t1_bracket (hlog : 1 ≤ Nat.log 2 d) :
    64 * Nat.log 2 d ≤ t1 d ∧ t1 d ≤ 128 * Nat.log 2 d := by
  refine ⟨le_ceilPowTwo _, ?_⟩
  have : ceilPowTwo (64 * Nat.log 2 d) ≤ 2 * (64 * Nat.log 2 d) :=
    ceilPowTwo_le_two_mul (by omega)
  unfold t1; omega

/-- The GATE `t₁ ≤ q₁ + 5` (S1fam_balanced / L1_pos consumer): holds once
`128 log d ≤ 2 (log d)²`, i.e. `log d ≥ 64`. -/
theorem t1_le_q1_add_five (hlog : 64 ≤ Nat.log 2 d) :
    t1 d ≤ q1 d + 5 := by
  have h1 : 1 ≤ Nat.log 2 d := by omega
  have ht : t1 d ≤ 128 * Nat.log 2 d := (t1_bracket h1).2
  have hq : 2 * Nat.log 2 d ^ 2 ≤ q1 d + 2 := le_q1_add_two h1
  have hkey : 128 * Nat.log 2 d ≤ 2 * Nat.log 2 d ^ 2 := by nlinarith
  omega

/-- The stronger GATE `t₁ ≤ q₁ + 2` (feeds the exact divisibility
`q₁ + 2 = r₁ · t₁`). -/
theorem t1_le_q1_add_two (hlog : 64 ≤ Nat.log 2 d) :
    t1 d ≤ q1 d + 2 := by
  have h1 : 1 ≤ Nat.log 2 d := by omega
  have ht : t1 d ≤ 128 * Nat.log 2 d := (t1_bracket h1).2
  have hq : 2 * Nat.log 2 d ^ 2 ≤ q1 d + 2 := le_q1_add_two h1
  have hkey : 128 * Nat.log 2 d ≤ 2 * Nat.log 2 d ^ 2 := by nlinarith
  omega

/-- The GATE `1 ≤ q₁` (S2fam_balanced / L2_pos consumer). -/
theorem one_le_q1 (hlog : 2 ≤ Nat.log 2 d) : 1 ≤ q1 d := by
  have h1 : 1 ≤ Nat.log 2 d := by omega
  have : 2 * 2 ^ 2 ≤ 2 * Nat.log 2 d ^ 2 := by nlinarith
  have := le_trans this (le_q1_add_two h1)
  omega

/-! ### Stage-2 parameters `q₂`, `t₂` -/

/-- `t₂ ≤ 6 log d` (upper bracket): the inner ℕ ceiling is `≤ 3 log d`
(`ceilDiv_le`, needs `loglog d ≥ 1`), and `ceilPowTwo` at most doubles. -/
theorem t2_le (hloglog : 1 ≤ Nat.log 2 (Nat.log 2 d)) :
    t2 d ≤ 6 * Nat.log 2 d := by
  set kk := Nat.log 2 (Nat.log 2 d) with hkk
  have hinner : (3 * Nat.log 2 d + kk - 1) / kk ≤ 3 * Nat.log 2 d :=
    ceilDiv_le hloglog
  have hlogd : 1 ≤ Nat.log 2 d := le_trans hloglog (Nat.log_le_self 2 _)
  have hbig : t2 d ≤ 2 * ((3 * Nat.log 2 d + kk - 1) / kk) := by
    unfold t2
    apply ceilPowTwo_le_two_mul
    have hnum : kk ≤ 3 * Nat.log 2 d + kk - 1 := by omega
    calc 1 = kk / kk := (Nat.div_self (by omega)).symm
      _ ≤ (3 * Nat.log 2 d + kk - 1) / kk := Nat.div_le_div_right hnum
  omega

/-- `t₂` positive lower bracket: `t₂ ≥ ⌈3 log d / loglog d⌉ ≥ 1` (already
have `t2_pos`); an explicit `log d ≤ t₂` will not be needed. -/
theorem one_le_t2 : 1 ≤ t2 d := t2_pos d

end Params

/-! ### Linear-vs-exponential growth (`c·k ≤ 2 ^ k` for large `k`) -/

/-- `6 k ≤ 2 ^ k` for `k ≥ 6`. Base `k = 6`: `36 ≤ 64`; step uses `k < 2^k`. -/
theorem six_mul_le_two_pow {k : ℕ} (hk : 6 ≤ k) : 6 * k ≤ 2 ^ k := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 6 with hn | hn
    · -- `hk : 6 ≤ n+1` forces `n = 5`
      have hn5 : n = 5 := by omega
      subst hn5; norm_num
    · have hih := ih hn
      have hlt : n < 2 ^ n := Nat.lt_two_pow_self
      have : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      omega

/-- `k ≤ 2 ^ k` (specialisation of `Nat.lt_two_pow_self`). -/
theorem le_two_pow_self (k : ℕ) : k ≤ 2 ^ k := le_of_lt Nat.lt_two_pow_self

/-- `3 ℓ² + ℓ + 1 ≤ 3 · 2^ℓ` for `ℓ ≥ 8` (polynomial dominated by the cubic
density budget `2^{3ℓ}`, evaluated through `t₂`). Base `ℓ = 8`: `201 ≤ 768`;
step uses `n < 2^n`. Consumed by `Params.t2_ge`. -/
theorem poly_le_exp {ℓ : ℕ} (hℓ : 8 ≤ ℓ) : 3 * ℓ ^ 2 + ℓ + 1 ≤ 3 * 2 ^ ℓ := by
  induction ℓ with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 8 with hn | hn
    · have hn7 : n = 7 := by omega
      subst hn7; norm_num
    · have hih := ih hn
      have hlt : n < 2 ^ n := Nat.lt_two_pow_self
      have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      nlinarith [hih, hlt]

/-- `m + 12 ≤ 2^m` for `m ≥ 6` (linear dominated by `2^m`). Base `m = 6`:
`18 ≤ 64`; step uses `2^{n+1} = 2·2^n`. Consumed by `Params.seed_slack`. -/
theorem add_le_two_pow {m : ℕ} (hm : 6 ≤ m) : m + 12 ≤ 2 ^ m := by
  induction m with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 6 with hn | hn
    · have hn5 : n = 5 := by omega
      subst hn5; norm_num
    · have hih := ih hn
      have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      omega

/-! ### The accuracy `ε_{q,t}` is small

`ε_{q,t} = (2qt)^{−c}` with `c = balancedFamilyConstant ≥ 1`, so for `q, t ≥ 1` it is at
most `1/(2qt)`; this is the single handle every density inequality uses to
drive `ε` below the constant gaps. -/

/-- `ε_{q,t} ≤ 1/(2qt)` for `q, t ≥ 1` (the `c ≥ 1` exponent bound). -/
theorem epsQT_le_inv {q t : ℕ} (hq : 0 < q) (ht : 0 < t) :
    epsQT q t ≤ 1 / (2 * (q : ℝ) * (t : ℝ)) := by
  unfold epsQT
  have hposN : 0 < 2 * q * t := by positivity
  have hbase1 : (1 : ℝ) ≤ ((2 * q * t : ℕ) : ℝ) := by exact_mod_cast hposN
  have hc : (1 : ℤ) ≤ (balancedFamilyConstant : ℤ) := by exact_mod_cast balancedFamilyConstant_pos
  have hmono : ((2 * q * t : ℕ) : ℝ) ^ (-(balancedFamilyConstant : ℤ))
      ≤ ((2 * q * t : ℕ) : ℝ) ^ (-(1 : ℤ)) :=
    zpow_le_zpow_right₀ hbase1 (by omega)
  refine le_trans hmono ?_
  rw [zpow_neg, zpow_one]
  push_cast
  ring_nf
  rfl

/-- `ε_{q,t} ≤ 1/2` for `q, t ≥ 1`. -/
theorem epsQT_le_half {q t : ℕ} (hq : 0 < q) (ht : 0 < t) :
    epsQT q t ≤ 1 / 2 := by
  refine le_trans (epsQT_le_inv hq ht) ?_
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- `ε_{q,t} ≤ 1/(2n)` whenever `n ≤ q·t` (`q,t ≥ 1`): the accuracy is driven
below any prescribed constant gap by the growth of `q·t`. -/
theorem epsQT_le_inv_mul {q t n : ℕ} (hq : 0 < q) (ht : 0 < t) (hn : n ≤ q * t)
    (hnpos : 0 < n) : epsQT q t ≤ 1 / (2 * (n : ℝ)) := by
  refine le_trans (epsQT_le_inv hq ht) ?_
  have hnR : (n : ℝ) ≤ (q : ℝ) * (t : ℝ) := by exact_mod_cast hn
  have hnpR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ### Column-family size lower bounds (via `aux:family-lower`)

`|C₁| = L₁`, `|C₂| = L₂`. The counting bound `|Y|^t/(1+ε) ≤ L` together with
`ε ≤ 1/2` gives the halved forms `|C₁| ≥ 2^{t₁-1}` and `|C₂| ≥ |R₁|^{t₂-1}`
that the density inequalities consume. -/

/-- `|C₁| ≥ 2^{t₁-1}`. With `t₁ ≥ 64 log d` this is the `|C₁| ≥ d^{64}/2` fact
of the ledger. -/
theorem L1_ge_pow (d : ℕ) (h : Params.t1 d ≤ Params.q1 d + 5) :
    ((2 : ℝ) ^ (Params.t1 d - 1)) ≤ (L1 d : ℝ) := by
  have hbal := S1fam_balanced d h
  have hq : 0 < Params.q1 d + 5 := by omega
  have hlow := balanced_family_card_lower hbal (epsQT_lt_one hq (Params.t1_pos d)) h
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by simp
  rw [hcard] at hlow
  have hε : epsQT (Params.q1 d + 5) (Params.t1 d) ≤ 1 / 2 :=
    epsQT_le_half hq (Params.t1_pos d)
  have hεpos : 0 < epsQT (Params.q1 d + 5) (Params.t1 d) :=
    epsQT_pos hq (Params.t1_pos d)
  have ht1pos : 1 ≤ Params.t1 d := Params.t1_pos d
  have hsplit : (2 : ℝ) ^ (Params.t1 d) = 2 * 2 ^ (Params.t1 d - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hnum : (0 : ℝ) < 2 ^ (Params.t1 d) := by positivity
  calc ((2 : ℝ) ^ (Params.t1 d - 1))
      = (2 : ℝ) ^ (Params.t1 d) / 2 := by rw [hsplit]; ring
    _ ≤ (2 : ℝ) ^ (Params.t1 d) / (1 + epsQT (Params.q1 d + 5) (Params.t1 d)) :=
        div_le_div_of_nonneg_left (le_of_lt hnum) (by linarith) (by linarith)
    _ ≤ (L1 d : ℝ) := hlow

/-- `|C₂| ≥ |R₁|^{t₂-1}` (with `|R₁| = q₁`). The paper's `|C₂| ≥ d^{6}/2`
follows from the exact `q₁^{t₂}`-vs-`d^{6}` log-log cancellation (a further
asymptotic step, flagged below); the halved-power form here is what the
fiber-survival density inequality directly consumes. -/
theorem L2_ge_pow (d : ℕ) (h : Params.t2 d ≤ Params.q2 d)
    (hq1 : 2 ≤ Params.q1 d) :
    ((Params.q1 d : ℝ) ^ (Params.t2 d - 1)) ≤ (L2 d : ℝ) := by
  have hbal := S2fam_balanced d h (by omega)
  have hlow := balanced_family_card_lower hbal
    (epsQT_lt_one (Params.q2_pos d) (Params.t2_pos d)) h
  have hcard : (Fintype.card (Fin (Params.q1 d) × Fin 1) : ℝ) = (Params.q1 d : ℝ) := by
    simp
  rw [hcard] at hlow
  have hε : epsQT (Params.q2 d) (Params.t2 d) ≤ 1 / 2 :=
    epsQT_le_half (Params.q2_pos d) (Params.t2_pos d)
  have hεpos : 0 < epsQT (Params.q2 d) (Params.t2 d) :=
    epsQT_pos (Params.q2_pos d) (Params.t2_pos d)
  have hq1R : (2 : ℝ) ≤ (Params.q1 d : ℝ) := by exact_mod_cast hq1
  have ht2pos : 1 ≤ Params.t2 d := Params.t2_pos d
  have hsplit : (Params.q1 d : ℝ) ^ (Params.t2 d)
      = (Params.q1 d : ℝ) * (Params.q1 d : ℝ) ^ (Params.t2 d - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hqpos : (0 : ℝ) < (Params.q1 d : ℝ) := by linarith
  have hbase_nonneg : (0 : ℝ) ≤ (Params.q1 d : ℝ) ^ (Params.t2 d - 1) :=
    pow_nonneg (le_of_lt hqpos) _
  -- `q1^{t2-1}·(1+ε) ≤ q1^{t2-1}·q1 = q1^{t2}`, hence divide.
  have hstep : (Params.q1 d : ℝ) ^ (Params.t2 d - 1)
      * (1 + epsQT (Params.q2 d) (Params.t2 d)) ≤ (Params.q1 d : ℝ) ^ (Params.t2 d) := by
    rw [hsplit]
    have : (1 : ℝ) + epsQT (Params.q2 d) (Params.t2 d) ≤ (Params.q1 d : ℝ) := by
      linarith
    nlinarith [hbase_nonneg]
  have hden : (0 : ℝ) < 1 + epsQT (Params.q2 d) (Params.t2 d) := by linarith
  calc ((Params.q1 d : ℝ) ^ (Params.t2 d - 1))
      = (Params.q1 d : ℝ) ^ (Params.t2 d - 1)
          * (1 + epsQT (Params.q2 d) (Params.t2 d))
          / (1 + epsQT (Params.q2 d) (Params.t2 d)) := by
        field_simp
    _ ≤ (Params.q1 d : ℝ) ^ (Params.t2 d)
          / (1 + epsQT (Params.q2 d) (Params.t2 d)) := by
        gcongr
    _ ≤ (L2 d : ℝ) := hlow

namespace Params

open NPCC

variable {d : ℕ}

/-- `q₂ = d` on powers of two (restatement of the VBP companion in the
`IsPow2` domain). -/
theorem q2_eq_of_pow2 (h : IsPow2 d) : q2 d = d := by
  obtain ⟨k, rfl⟩ := h; exact q2_eq_self rfl

/-- The GATE `t₂ ≤ q₂` (S2fam_balanced / L2_pos consumer): `t₂ ≤ 6 log d` and
`q₂ = d = 2^{log d} ≥ 6 log d` for `log d ≥ 6`. -/
theorem t2_le_q2 (h : IsPow2 d) (hlog : 6 ≤ Nat.log 2 d) : t2 d ≤ q2 d := by
  obtain ⟨k, rfl⟩ := h
  rw [q2_eq_self rfl, log_two_pow] at *
  have ht2 : t2 (2 ^ k) ≤ 6 * k := by
    have : 1 ≤ Nat.log 2 (Nat.log 2 (2 ^ k)) := by
      rw [log_two_pow]; exact Nat.log_pos (by norm_num) (by omega)
    have h6 := t2_le (d := 2 ^ k) this
    rwa [log_two_pow] at h6
  exact le_trans ht2 (le_trans (six_mul_le_two_pow hlog) (le_refl _))

/-- The GATE `t₂ ≤ 2 ^ b₁` (hard-seed side condition `t₂ ≤ 2^{b₁}`, feeds
`lem:M2-hard-seed`). `b₁ = 2 log d`, and `t₂ ≤ 6 log d ≤ 2^{2 log d}`. -/
theorem t2_le_pow_b1 (hlog : 6 ≤ Nat.log 2 d) : t2 d ≤ 2 ^ b1 d := by
  have hloglog : 1 ≤ Nat.log 2 (Nat.log 2 d) :=
    Nat.log_pos (by norm_num) (by omega)
  have ht2 : t2 d ≤ 6 * Nat.log 2 d := t2_le hloglog
  have hb : 6 * Nat.log 2 d ≤ 2 ^ (2 * Nat.log 2 d) := by
    have h1 : 6 * Nat.log 2 d ≤ 2 ^ (Nat.log 2 d) :=
      six_mul_le_two_pow hlog
    have h2 : 2 ^ (Nat.log 2 d) ≤ 2 ^ (2 * Nat.log 2 d) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    exact le_trans h1 h2
  unfold b1; omega

/-- EXACT divisibility fact `q₂ = r₂ · t₂` (`r₂ := q₂ / t₂`): both `q₂` and
`t₂` are powers of two and `t₂ ≤ q₂`, so `t₂ ∣ q₂`. -/
theorem q2_eq_r2_mul_t2 (h : IsPow2 d) (hlog : 6 ≤ Nat.log 2 d) :
    q2 d = r2 d * t2 d := by
  have hle : t2 d ≤ q2 d := t2_le_q2 h hlog
  have hdvd : t2 d ∣ q2 d := by
    rw [q2, t2] at *
    exact pow_two_dvd_of_le hle
  rw [r2]
  exact (Nat.div_mul_cancel hdvd).symm

/-- EXACT divisibility fact `q₁ + 2 = r₁ · t₁` (`r₁ := (q₁+2) / t₁`): both
`q₁+2` and `t₁` are powers of two and `t₁ ≤ q₁+2`, so `t₁ ∣ (q₁+2)`. -/
theorem q1_add_two_eq_r1_mul_t1 (hlog : 64 ≤ Nat.log 2 d) :
    q1 d + 2 = r1 d * t1 d := by
  have h1 : 1 ≤ Nat.log 2 d := by omega
  have hle : t1 d ≤ q1 d + 2 := t1_le_q1_add_two hlog
  have hdvd : t1 d ∣ (q1 d + 2) := by
    rw [q1_add_two_pow h1, t1] at *
    exact pow_two_dvd_of_le hle
  rw [r1]
  exact (Nat.div_mul_cancel hdvd).symm

/-- EXACT `⌈log q₂⌉ = log q₂` (D3): `q₂ = d = 2^{log d}`, so both `Nat.clog`
and `Nat.log` return `log d`. -/
theorem clog_q2_eq_log_q2 (h : IsPow2 d) :
    Nat.clog 2 (q2 d) = Nat.log 2 (q2 d) := by
  obtain ⟨k, rfl⟩ := h
  rw [q2_eq_self rfl, Nat.clog_pow 2 k (by norm_num), log_two_pow]

/-- Positivity of `loglog d` (D3 "positivity of loglog d"): for `log d ≥ 2`,
`Nat.log 2 (Nat.log 2 d) ≥ 1`. -/
theorem loglog_pos (hlog : 2 ≤ Nat.log 2 d) : 1 ≤ Nat.log 2 (Nat.log 2 d) :=
  Nat.log_pos (by norm_num) (by omega)

/-! ### Real density auxiliaries `η₂`, `h₂↓` -/

/-- `η₂ := q₂ · 2^{−R₁+1}` (paper; real form). -/
noncomputable def eta2 (d : ℕ) : ℝ := (q2 d : ℝ) * (2 : ℝ) ^ (-(b1 d : ℤ) + 1)

/-- On powers of two, `η₂ = 2^{1 − log d}`. -/
theorem eta2_eq (h : IsPow2 d) : eta2 d = (2 : ℝ) ^ (1 - (Nat.log 2 d : ℤ)) := by
  obtain ⟨k, rfl⟩ := h
  unfold eta2
  rw [q2_eq_self rfl, log_two_pow]
  have hb1 : b1 (2 ^ k) = 2 * k := by unfold b1; rw [log_two_pow]
  rw [hb1]
  have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ (k : ℤ) := by
    rw [zpow_natCast]; push_cast; ring
  rw [hcast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  push_cast; ring

/-- `η₂ > 0`. -/
theorem eta2_pos : 0 < eta2 d := by
  unfold eta2
  have h1 : (0 : ℝ) < (q2 d : ℝ) := by exact_mod_cast q2_pos d
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (-(b1 d : ℤ) + 1) := by positivity
  positivity

/-- `η₂ ≤ 1/2` on powers of two with `log d ≥ 2`. -/
theorem eta2_le_half (h : IsPow2 d) (hlog : 2 ≤ Nat.log 2 d) : eta2 d ≤ 1 / 2 := by
  rw [eta2_eq h, show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℤ) by norm_num]
  apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  omega

/-- `η₂ ≤ 2^{-1}·(anything ≥ 1)` — a convenient `η₂ ≤ small` handle: for
`log d ≥ N+1`, `η₂ ≤ 2^{-N}`. -/
theorem eta2_le_pow (h : IsPow2 d) {N : ℕ} (hlog : (N : ℤ) + 1 ≤ Nat.log 2 d) :
    eta2 d ≤ (2 : ℝ) ^ (-(N : ℤ)) := by
  rw [eta2_eq h]
  apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  omega

/-- `h₂ ≤ 2^{−3 loglog d}` (exact: `h₂ = 2^{−b₂}`, `b₂ = 3 loglog d`), so for
`loglog d ≥ M`, `h₂ ≤ 2^{−3M}`. -/
theorem h2_le_pow {M : ℕ} (hM : M ≤ Nat.log 2 (Nat.log 2 d)) :
    h2 d ≤ (2 : ℝ) ^ (-(3 * M : ℤ)) := by
  unfold h2 b2
  apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  omega

/-- `h₂ > 0`. -/
theorem h2_pos : 0 < h2 d := by unfold h2; positivity

/-- Exact `h₂ = 2^{−3 loglog d}` (unfolds `h₂ = 2^{−b₂}`, `b₂ = 3 loglog d`).
The C.1 Stage-3 estimate needs the exact exponent (not just an upper bound). -/
theorem h2_eq : h2 d = (2 : ℝ) ^ (-(3 * Nat.log 2 (Nat.log 2 d) : ℤ)) := by
  unfold h2 b2; norm_num

/-- Upper bracket `q₁ ≤ 4 log² d` (restatement of `q1_add_two_le`). Feeds the
Stage-3 fiber-survival density inequality (App C.1 row 3). -/
theorem q1_le (hlog : 1 ≤ Nat.log 2 d) : q1 d ≤ 4 * Nat.log 2 d ^ 2 := by
  have := q1_add_two_le hlog; omega

/-- `t₂` lower bracket `3 loglog d + 2 ≤ t₂` (for `log d ≥ 256`, hence
`loglog d ≥ 8`). Via `t₂ ≥ ⌈3 log d / loglog d⌉ ≥ 3 loglog d + 2`, using
`(loglog d)²` dominated by `log d` (`poly_le_exp` through `2^{loglog d} ≤ log
d`). Consumed by the C.1 Stage-3 estimate `3⌈2^{−b₂+1}|C₂|⌉ ≤ 8h₂|C₂|`. -/
theorem t2_ge (hlog : (256 : ℕ) ≤ Nat.log 2 d) :
    3 * Nat.log 2 (Nat.log 2 d) + 2 ≤ t2 d := by
  set L := Nat.log 2 d with hL
  set ℓ := Nat.log 2 L with hℓ
  have hℓ8 : 8 ≤ ℓ := by
    rw [hℓ]
    calc 8 = Nat.log 2 256 := by norm_num [Nat.log]
      _ ≤ Nat.log 2 L := Nat.log_mono_right hlog
  have hℓpos : 0 < ℓ := by omega
  have hpow_le : 2 ^ ℓ ≤ L := Nat.pow_log_le_self 2 (by omega)
  have hpoly : 3 * ℓ ^ 2 + ℓ + 1 ≤ 3 * 2 ^ ℓ := poly_le_exp hℓ8
  have hkey : 3 * ℓ ^ 2 + ℓ + 1 ≤ 3 * L := le_trans hpoly (by omega)
  have hexp : (3 * ℓ + 2) * ℓ = 3 * ℓ ^ 2 + 2 * ℓ := by ring
  have hcore : (3 * ℓ + 2) * ℓ ≤ 3 * L + ℓ - 1 := by rw [hexp]; omega
  have hdiv : 3 * ℓ + 2 ≤ (3 * L + ℓ - 1) / ℓ := by
    rw [Nat.le_div_iff_mul_le hℓpos]; omega
  have ht2 : (3 * L + ℓ - 1) / ℓ ≤ t2 d := by
    unfold t2; rw [← hL, ← hℓ]; exact le_ceilPowTwo _
  omega

/-- The Stage-2 hard-seed slack inequality (paper `sec:scaffold`, Stage-1/
Stage-2 bootstrap, "Hard seed"/"Seed comparison", main.tex l.6952–6958):
`3 log d + ⌈log(16 t₁)⌉ + 1 ≤ t₁ / 16`, rendered division-free as
`16 (3 log d + log(16 t₁) + 1) ≤ t₁`. This is the integer log-form of the
seed comparison `(9/16)t₁ − 3 log d − log(16 t₁) > (1/2)t₁` that makes the
localized-extension bridge `h_seed ≤ h₂↓ · 2^{−(log t₁ + comp M₀)}/(1+ε)`
have slack at the residual density `h₂↓ = 2^{−(b₁+log r₂)}` with
`p_seed = (9/16)t₁`. Discharges at `log d ≥ 64`: `t₁/16 ≥ 4 log d` dominates
`3 log d + O(log log d)`. -/
theorem seed_slack (hlog : 64 ≤ Nat.log 2 d) :
    16 * (3 * Nat.log 2 d + Nat.log 2 (16 * t1 d) + 1) ≤ t1 d := by
  have h1 : 1 ≤ Nat.log 2 d := by omega
  have htlo : 64 * Nat.log 2 d ≤ t1 d := (t1_bracket h1).1
  have hthi : t1 d ≤ 128 * Nat.log 2 d := (t1_bracket h1).2
  -- 16 t₁ ≤ 2¹¹ · log d < 2^{12 + log(log d)}.
  have hb : 16 * t1 d ≤ 2 ^ 11 * Nat.log 2 d := by
    have hmul : 16 * t1 d ≤ 16 * (128 * Nat.log 2 d) := Nat.mul_le_mul_left 16 hthi
    have : (2:ℕ) ^ 11 = 2048 := by norm_num
    omega
  have hLlt : Nat.log 2 d < 2 ^ (Nat.log 2 (Nat.log 2 d) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hbnd : 16 * t1 d < 2 ^ (12 + Nat.log 2 (Nat.log 2 d)) := by
    calc 16 * t1 d ≤ 2 ^ 11 * Nat.log 2 d := hb
      _ < 2 ^ 11 * 2 ^ (Nat.log 2 (Nat.log 2 d) + 1) :=
          (Nat.mul_lt_mul_left (by norm_num)).mpr hLlt
      _ = 2 ^ (12 + Nat.log 2 (Nat.log 2 d)) := by rw [← pow_add]; congr 1; omega
  -- hence log(16 t₁) ≤ 11 + log(log d)
  have hlog16t1 : Nat.log 2 (16 * t1 d) ≤ 11 + Nat.log 2 (Nat.log 2 d) := by
    have hpos : (0:ℕ) < 16 * t1 d := by have := t1_pos d; omega
    have hlt := Nat.log_lt_of_lt_pow (b := 2) (x := 12 + Nat.log 2 (Nat.log 2 d))
      (y := 16 * t1 d) hpos.ne' hbnd
    omega
  -- 12 + log(log d) ≤ log d, via `add_le_two_pow` and `2^{loglog d} ≤ log d`.
  have hll_small : 12 + Nat.log 2 (Nat.log 2 d) ≤ Nat.log 2 d := by
    have hpow : 2 ^ Nat.log 2 (Nat.log 2 d) ≤ Nat.log 2 d :=
      Nat.pow_log_le_self 2 (by omega)
    -- if loglog d ≥ 6, add_le_two_pow gives loglog d + 12 ≤ 2^{loglog d} ≤ log d;
    -- if loglog d < 6, then 12 + loglog d ≤ 17 ≤ 64 ≤ log d directly.
    rcases Nat.lt_or_ge (Nat.log 2 (Nat.log 2 d)) 6 with hsmall | hbig
    · omega
    · have := add_le_two_pow hbig; omega
  omega

end Params

/-! ## The bundled checklist `Checklist d`

Every recurring large-`d` fact the transfer layer and Stages 2–4 consume,
gathered into one `Prop`. Grouped: (A) the discrete endpoint/divisibility/
exactness gates consumed by the construction; (B) the
column-family size floors; (C) the App C.1 density-domination table. The
deliverable theorem `large_d_checklist` exhibits an explicit power-of-two
witness `d₀` with `∀ d ≥ d₀ (a power of two), Checklist d` before `d_star`
uses `Classical.choice`. -/

open Params

/-- The bundled large-`d` checklist over a (power-of-two) ambient dimension
`d`. -/
structure Checklist (d : ℕ) : Prop where
  /-- (A1) GATE `t₁ ≤ q₁ + 5` (S1fam_balanced / L1_pos). -/
  t1_le_q1_add_five : t1 d ≤ q1 d + 5
  /-- (A2) GATE `1 ≤ q₁` (S2fam_balanced / L2_pos). -/
  one_le_q1 : 1 ≤ q1 d
  /-- (A3) GATE `t₂ ≤ q₂` (S2fam_balanced / L2_pos). -/
  t2_le_q2 : t2 d ≤ q2 d
  /-- (A4) GATE `t₂ ≤ 2^{b₁}` (hard-seed side condition). -/
  t2_le_pow_b1 : t2 d ≤ 2 ^ b1 d
  /-- (A5) EXACT divisibility `q₁ + 2 = r₁ · t₁`. -/
  q1_add_two_eq : q1 d + 2 = r1 d * t1 d
  /-- (A6) EXACT divisibility `q₂ = r₂ · t₂`. -/
  q2_eq : q2 d = r2 d * t2 d
  /-- (A7) EXACT `⌈log q₂⌉ = log q₂`. -/
  clog_q2_eq : Nat.clog 2 (q2 d) = Nat.log 2 (q2 d)
  /-- (A8) `q₂ = d`. -/
  q2_eq_self : q2 d = d
  /-- (A9) positivity of `loglog d`. -/
  loglog_pos : 1 ≤ Nat.log 2 (Nat.log 2 d)
  /-- (A10) `comp M₁ = a + 1 ≥ 3` is feasible: `a d ≥ 2`. -/
  a_ge_two : 2 ≤ a d
  /-- (B1) `|C₁| ≥ 2^{t₁-1}` (the `d^{64}/2` floor). -/
  L1_ge : ((2 : ℝ) ^ (t1 d - 1)) ≤ (L1 d : ℝ)
  /-- (B2) `|C₂| ≥ |R₁|^{t₂-1}` (the `d^{6}/2` floor). -/
  L2_ge : ((q1 d : ℝ) ^ (t2 d - 1)) ≤ (L2 d : ℝ)
  /-- (C1) `2(½+δ)² ≤ 1/(1+ε_{q₂,t₂})` (Stage-2 relaxed near-exact
  separation; App C.1 row 1a). -/
  dens_sep : 2 * (1 / 2 + delta) ^ 2 ≤ 1 / (1 + epsQT (q2 d) (t2 d))
  /-- (C2) `2(½+δ)² ≤ σ/(1+ε_{q₂,t₂})` for all `σ ≥ 1 − 8h₂` (projected
  dense-row variant; App C.1 row 2). -/
  dens_sep_dense : ∀ σ : ℝ, 1 - 8 * h2 d ≤ σ →
    2 * (1 / 2 + delta) ^ 2 ≤ σ / (1 + epsQT (q2 d) (t2 d))
  /-- (C3) `η₂ < (1 − ε_{2^a+3,t₁})/2` (final chosen-coordinate Stage-1
  threshold; App C.1 row 6). -/
  dens_eta_lt : eta2 d < (1 - epsQT (2 ^ a d + 3) (t1 d)) / 2
  /-- (C4) `1 − η₂ ≥ h₂↓` where `h₂↓ := 2^{−(b₁ + log r₂)}` (surviving Stage-2
  columns dense enough; App C.1 row 4). -/
  dens_survive : (2 : ℝ) ^ (-((b1 d : ℤ) + Nat.log 2 (r2 d))) ≤ 1 - eta2 d
  /-- (C5) `q₂·⌈2^{−b₁+1}·|C₁|⌉ < |C₁|` (Stage-2 relaxed near-exact separation,
  the dominant-block feasibility half of App C.1 row 1; main.tex l.6531,
  proof l.3940–3947). The ceiling `⌈2^{−b₁+1}|C₁|⌉` is over ℝ (rendered
  `Nat.ceil`); `2^{−b₁+1}` is the real fiber-density scale, `|C₁| = L₁`. -/
  dens_dominant_count :
    (q2 d : ℝ) * (⌈(2 : ℝ) ^ (-(b1 d : ℤ) + 1) * (L1 d : ℝ)⌉₊ : ℝ) < (L1 d : ℝ)
  /-- (C6) `8h₂ < (1 − ε_{q₂,t₂})/|R₁|` with `|R₁| = q₁` (every projected
  Stage-1 row type survives the Stage-3 row loss, the `C2FiberSurvival` feeder;
  App C.1 row 3, main.tex l.6541). -/
  dens_fiber_survival :
    8 * h2 d < (1 - epsQT (q2 d) (t2 d)) / (q1 d : ℝ)
  /-- (C7) `(q₂−1)(2^{−b₁+1}|C₁|+1) < η₂|C₁|` (the non-dominant Stage-2
  rectangles cannot cover too much of the chosen block `X̂_{p,α}`; App C.1
  row 5, main.tex l.6551, proof l.4995/l.5058). `η₂ = q₂·2^{−b₁+1}`, so the
  RHS is `q₂·2^{−b₁+1}|C₁|`; the inequality is one column-worth of slack. -/
  dens_nondominant_slack :
    ((q2 d : ℝ) - 1) * ((2 : ℝ) ^ (-(b1 d : ℤ) + 1) * (L1 d : ℝ) + 1)
      < eta2 d * (L1 d : ℝ)
  /-- (C8) `3⌈2^{−b₂+1}·|C₂|⌉ ≤ 8h₂·|C₂|` (the Stage-3 row loss rewritten in the
  clean density form `(1−8h₂)|C₂|`; main.tex l.3249–3252). `2^{−b₂+1} = 2h₂`,
  `|C₂| = L₂`; the ceiling is over ℝ (`Nat.ceil`). -/
  dens_stage3_rowloss :
    3 * (⌈(2 : ℝ) ^ (-(b2 d : ℤ) + 1) * (L2 d : ℝ)⌉₊ : ℝ) ≤ 8 * h2 d * (L2 d : ℝ)
  /-- (C9) `16(3 log d + log(16 t₁) + 1) ≤ t₁` — the Stage-2 hard-seed slack
  inequality (the integer log-form of the seed comparison `(9/16)t₁ − 3 log d −
  log(16 t₁) > (1/2)t₁`; paper `sec:scaffold` Stage-1/Stage-2 bootstrap,
  main.tex l.6952–6958). It makes the localized-extension bridge
  `h_seed ≤ h₂↓·2^{−(log t₁ + comp M₀)}/(1+ε)` have slack at the residual
  density `h₂↓ = 2^{−(b₁+log r₂)}` with `p_seed = (9/16)t₁`. -/
  seed_slack :
    16 * (3 * Nat.log 2 d + Nat.log 2 (16 * t1 d) + 1) ≤ t1 d

/-! ## The deliverable: the checklist holds for all large powers of two -/

-- CLAIM-BEGIN lem:large-d-checklist
set_option maxHeartbeats 1600000 in
/-- **`lem:large-d-checklist`** (existential-threshold / Nonempty form, D3):
there is an explicit power-of-two threshold `d₀ = 2^{256}` such that every
power of two `d ≥ d₀` satisfies the bundled `Checklist`. The witness is the
huge explicit `d₀` (hard-seed `m₀`-witness pattern); this is exactly the
`Nonempty` fact D3 requires proved BEFORE `d_star` is extracted by
`Classical.choice`.

Witness raised `2^{64} → 2^{256}` (from the original two-conjunct bundle) by
the NEW binding constraint: the App C.1 fiber-survival inequality
`8h₂ < (1−ε₂)/|R₁|` (field `dens_fiber_survival`) needs `loglog d ≥ 8`, i.e.
`log d ≥ 256`, so that `q₁ = Θ(log² d)` is dominated by
`1/h₂ = 2^{3 loglog d}`. Every other field holds already at `log d ≥ 64` and
is monotone upward; the explicit-witness pattern absorbs the raise. -/
theorem large_d_checklist :
    ∃ d₀ : ℕ, ∀ d : ℕ, IsPow2 d → d₀ ≤ d → Checklist d := by
  refine ⟨2 ^ 256, ?_⟩
  intro d hpow hge
  obtain ⟨k, rfl⟩ := hpow
  -- `2^256 ≤ 2^k` forces `k ≥ 256`.
  have hk : 256 ≤ k := by
    by_contra hlt
    have hlt' : k < 256 := by omega
    have : (2 : ℕ) ^ k < 2 ^ 256 := Nat.pow_lt_pow_right (by norm_num) hlt'
    omega
  have hlogk : Nat.log 2 (2 ^ k) = k := log_two_pow k
  have hlog256 : 256 ≤ Nat.log 2 (2 ^ k) := by rw [hlogk]; exact hk
  have hlog64 : 64 ≤ Nat.log 2 (2 ^ k) := by omega
  have hlog2 : 2 ≤ Nat.log 2 (2 ^ k) := by omega
  have hlog6 : 6 ≤ Nat.log 2 (2 ^ k) := by omega
  have hloglog : 1 ≤ Nat.log 2 (Nat.log 2 (2 ^ k)) :=
    Params.loglog_pos hlog2
  -- loglog (2^k) = log k ≥ log 256 = 8 (since k ≥ 256)
  have hloglog8 : 8 ≤ Nat.log 2 (Nat.log 2 (2 ^ k)) := by
    rw [hlogk]
    calc 8 = Nat.log 2 256 := by norm_num [Nat.log]
      _ ≤ Nat.log 2 k := Nat.log_mono_right hk
  have hloglog6 : 6 ≤ Nat.log 2 (Nat.log 2 (2 ^ k)) := by omega
  have hpow2 : IsPow2 (2 ^ k) := ⟨k, rfl⟩
  -- accuracy handles: ε₂ ≤ 1/4 (n = 2 ≤ q₂·t₂), ε₁ ≤ 1/4.
  have hq2t2 : (2 : ℕ) ≤ q2 (2 ^ k) * t2 (2 ^ k) := by
    have : 2 ≤ q2 (2 ^ k) := by
      rw [q2_eq_self rfl]; exact Nat.one_lt_two_pow (by omega)
    have ht2 : 1 ≤ t2 (2 ^ k) := t2_pos _
    calc 2 ≤ q2 (2 ^ k) := this
      _ = q2 (2 ^ k) * 1 := (Nat.mul_one _).symm
      _ ≤ q2 (2 ^ k) * t2 (2 ^ k) := by gcongr
  have hε2 : epsQT (q2 (2 ^ k)) (t2 (2 ^ k)) ≤ 1 / 4 := by
    have := epsQT_le_inv_mul (q2_pos _) (t2_pos _) hq2t2 (by norm_num)
    simpa using this.trans (by norm_num)
  have hε2pos : 0 < epsQT (q2 (2 ^ k)) (t2 (2 ^ k)) :=
    epsQT_pos (q2_pos _) (t2_pos _)
  -- ε₁ = epsQT (2^a+3) t1 ≤ 1/4
  have hε1n : (2 : ℕ) ≤ (2 ^ a (2 ^ k) + 3) * t1 (2 ^ k) := by
    have : 1 ≤ t1 (2 ^ k) := t1_pos _
    nlinarith [Nat.one_le_iff_ne_zero.mpr (by positivity : (2:ℕ) ^ a (2^k) ≠ 0)]
  have hε1 : epsQT (2 ^ a (2 ^ k) + 3) (t1 (2 ^ k)) ≤ 1 / 4 := by
    have := epsQT_le_inv_mul (q := 2 ^ a (2 ^ k) + 3) (t := t1 (2 ^ k))
      (by positivity) (t1_pos _) hε1n (by norm_num)
    simpa using this.trans (by norm_num)
  have hε1pos : 0 < epsQT (2 ^ a (2 ^ k) + 3) (t1 (2 ^ k)) :=
    epsQT_pos (by positivity) (t1_pos _)
  -- `8 h₂ ≤ 1/32`
  have hh2 : 8 * h2 (2 ^ k) ≤ 1 / 32 := by
    have hb := h2_le_pow (M := 6) hloglog6
    have hval : (2 : ℝ) ^ (-(3 * (6 : ℕ) : ℤ)) = 1 / 262144 := by norm_num
    rw [hval] at hb
    nlinarith [h2_pos (d := 2 ^ k)]
  -- Shared handles for the App C.1 density/count fields (C5–C8).
  -- `b₁ = 2k`, `t₁ ≥ 64k`, `q₂ = 2^k`, `2 ≤ q₁ ≤ 4k²`, and the size floors.
  have hb1 : b1 (2 ^ k) = 2 * k := by unfold b1; rw [hlogk]
  have ht1lo : 64 * k ≤ t1 (2 ^ k) := by
    have := (Params.t1_bracket (d := 2 ^ k) (by omega)).1; rwa [hlogk] at this
  have hq2eq : q2 (2 ^ k) = 2 ^ k := q2_eq_self rfl
  have hq1ge2 : 2 ≤ q1 (2 ^ k) := by
    have := Params.le_q1_add_two (d := 2 ^ k) (by omega); rw [hlogk] at this; nlinarith
  have hq1le : q1 (2 ^ k) ≤ 4 * k ^ 2 := by
    have := Params.q1_le (d := 2 ^ k) (by omega); rwa [hlogk] at this
  -- size floors  |C₁| ≥ 2^{t₁-1}  and  |C₂| ≥ q₁^{t₂-1}
  have hL1floor : ((2 : ℝ) ^ (t1 (2 ^ k) - 1)) ≤ (L1 (2 ^ k) : ℝ) :=
    L1_ge_pow _ (Params.t1_le_q1_add_five hlog64)
  have hL2floor : ((q1 (2 ^ k) : ℝ) ^ (t2 (2 ^ k) - 1)) ≤ (L2 (2 ^ k) : ℝ) :=
    L2_ge_pow _ (Params.t2_le_q2 hpow2 hlog6) hq1ge2
  have hL1pos : 0 < L1 (2 ^ k) := L1_pos _ (Params.t1_le_q1_add_five hlog64)
  have hL2pos : 0 < L2 (2 ^ k) := L2_pos _ (Params.t2_le_q2 hpow2 hlog6) (by omega)
  refine
    { t1_le_q1_add_five := Params.t1_le_q1_add_five hlog64
      one_le_q1 := Params.one_le_q1 hlog2
      t2_le_q2 := Params.t2_le_q2 hpow2 hlog6
      t2_le_pow_b1 := Params.t2_le_pow_b1 hlog6
      q1_add_two_eq := Params.q1_add_two_eq_r1_mul_t1 hlog64
      q2_eq := Params.q2_eq_r2_mul_t2 hpow2 hlog6
      clog_q2_eq := Params.clog_q2_eq_log_q2 hpow2
      q2_eq_self := q2_eq_self rfl
      loglog_pos := hloglog
      a_ge_two := ?_
      L1_ge := L1_ge_pow _ (Params.t1_le_q1_add_five hlog64)
      L2_ge := L2_ge_pow _ (Params.t2_le_q2 hpow2 hlog6) ?_
      dens_sep := ?_
      dens_sep_dense := ?_
      dens_eta_lt := ?_
      dens_survive := ?_
      dens_dominant_count := ?_
      dens_fiber_survival := ?_
      dens_nondominant_slack := ?_
      dens_stage3_rowloss := ?_
      seed_slack := Params.seed_slack hlog64 }
  · -- a ≥ 2 : 2^a = q1+2 ≥ 2 log²d ≥ 2·64² ≥ 2^13, so a ≥ 13 ≥ 2
    have h2a : q1 (2 ^ k) + 2 = 2 ^ a (2 ^ k) := Params.q1_add_two_pow (by omega)
    have hlow : 2 * Nat.log 2 (2 ^ k) ^ 2 ≤ q1 (2 ^ k) + 2 :=
      Params.le_q1_add_two (by omega)
    rw [h2a] at hlow
    rw [hlogk] at hlow
    have hbig : (2 : ℕ) ^ 2 ≤ 2 ^ a (2 ^ k) := by
      calc (2 : ℕ) ^ 2 = 4 := by norm_num
        _ ≤ 2 * k ^ 2 := by nlinarith
        _ ≤ 2 ^ a (2 ^ k) := hlow
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hbig
  · -- 2 ≤ q1 for L2
    have := Params.le_q1_add_two (d := 2 ^ k) (by omega)
    rw [hlogk] at this
    nlinarith
  · -- dens_sep : 0.72 ≤ 1/(1+ε₂)
    have : 2 * (1 / 2 + delta) ^ 2 = 0.72 := by unfold delta; norm_num
    rw [this]
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  · -- dens_sep_dense
    intro σ hσ
    have hσlb : (0.95 : ℝ) ≤ σ := by
      have : (1 : ℝ) - 8 * h2 (2 ^ k) ≤ σ := hσ
      linarith
    have hval : 2 * (1 / 2 + delta) ^ 2 = 0.72 := by unfold delta; norm_num
    rw [hval, le_div_iff₀ (by linarith)]
    nlinarith
  · -- dens_eta_lt : η₂ < (1-ε₁)/2
    have hη : eta2 (2 ^ k) ≤ (2 : ℝ) ^ (-(2 : ℤ)) := by
      have := Params.eta2_le_pow (d := 2 ^ k) hpow2 (N := 2) (by rw [hlogk]; omega)
      simpa using this
    have hηval : (2 : ℝ) ^ (-(2 : ℤ)) = 1 / 4 := by norm_num
    rw [hηval] at hη
    rw [lt_div_iff₀ (by norm_num)]
    nlinarith
  · -- dens_survive : 2^{-(b1+log r2)} ≤ 1 - η₂
    have hη : eta2 (2 ^ k) ≤ 1 / 2 := Params.eta2_le_half hpow2 hlog2
    have hlhs : (2 : ℝ) ^ (-((b1 (2 ^ k) : ℤ) + Nat.log 2 (r2 (2 ^ k)))) ≤ 1 / 2 := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℤ) by norm_num]
      apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      have hb1' : 1 ≤ b1 (2 ^ k) := by
        unfold b1; rw [hlogk]; omega
      omega
    linarith
  · -- (C5) dens_dominant_count : q₂·⌈2^{−b₁+1}·L₁⌉ < L₁
    -- X := 2^{1−2k}·L₁ ≥ 2^{62k} ≥ 1, ⌈X⌉ ≤ 2X, q₂·2X = 2^{2−k}·L₁ < L₁.
    set L1R := (L1 (2 ^ k) : ℝ) with hL1R
    have hL1Rpos : (0 : ℝ) < L1R := by rw [hL1R]; exact_mod_cast hL1pos
    -- 2^{−b₁+1} = 2^{1−2k} (real zpow)
    have hscale : (2 : ℝ) ^ (-(b1 (2 ^ k) : ℤ) + 1) = (2 : ℝ) ^ (1 - 2 * (k : ℤ)) := by
      rw [hb1]; congr 1; push_cast; ring
    rw [hscale, hq2eq, show (((2 ^ k : ℕ) : ℝ)) = (2 : ℝ) ^ k from by push_cast; ring]
    set X := (2 : ℝ) ^ (1 - 2 * (k : ℤ)) * L1R with hX
    -- L₁ ≥ 2^{t₁−1} ≥ 2^{64k−1}, so X ≥ 2^{1−2k}·2^{64k−1} = 2^{62k} ≥ 1.
    have hpowcast : (2 : ℝ) ^ (t1 (2 ^ k) - 1) = (2 : ℝ) ^ ((t1 (2 ^ k) : ℤ) - 1) := by
      rw [← zpow_natCast]; congr 1; have := t1_pos (2 ^ k); omega
    have hXge1 : (1 : ℝ) ≤ X := by
      have hfloor : (2 : ℝ) ^ ((64 * k : ℤ) - 1) ≤ L1R := by
        rw [hL1R]
        refine le_trans ?_ hL1floor
        rw [hpowcast]
        apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        have : (64 : ℤ) * k ≤ t1 (2 ^ k) := by exact_mod_cast ht1lo
        omega
      have hstep : (2 : ℝ) ^ (1 - 2 * (k : ℤ)) * (2 : ℝ) ^ ((64 * k : ℤ) - 1)
          = (2 : ℝ) ^ (62 * (k : ℤ)) := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
      have hbig : (1 : ℝ) ≤ (2 : ℝ) ^ (62 * (k : ℤ)) := by
        apply one_le_zpow₀ (by norm_num : (1 : ℝ) ≤ 2); positivity
      calc (1 : ℝ) ≤ (2 : ℝ) ^ (62 * (k : ℤ)) := hbig
        _ = (2 : ℝ) ^ (1 - 2 * (k : ℤ)) * (2 : ℝ) ^ ((64 * k : ℤ) - 1) := hstep.symm
        _ ≤ (2 : ℝ) ^ (1 - 2 * (k : ℤ)) * L1R := by
            apply mul_le_mul_of_nonneg_left hfloor (by positivity)
    -- ⌈X⌉ ≤ X + 1 ≤ 2X
    have hceil : (⌈X⌉₊ : ℝ) ≤ 2 * X := by
      have h1 : (⌈X⌉₊ : ℝ) < X + 1 := Nat.ceil_lt_add_one (by linarith)
      linarith
    -- 2^k · 2X = 2^{2−k}·L₁ < L₁
    have hq2X : (2 : ℝ) ^ k * (2 * X) = (2 : ℝ) ^ (2 - (k : ℤ)) * L1R := by
      rw [hX]
      have hkcast : (2 : ℝ) ^ k = (2 : ℝ) ^ (k : ℤ) := by rw [zpow_natCast]
      rw [hkcast, show (2 : ℝ) * ((2 : ℝ) ^ (1 - 2 * (k : ℤ)) * L1R)
            = (2 : ℝ) ^ (1 : ℤ) * (2 : ℝ) ^ (1 - 2 * (k : ℤ)) * L1R by
          rw [zpow_one]; ring]
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
          ← mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 2; ring
    have hlt : (2 : ℝ) ^ (2 - (k : ℤ)) * L1R < L1R := by
      have hsmall : (2 : ℝ) ^ (2 - (k : ℤ)) < 1 := by
        rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℤ) by norm_num]
        apply zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2)
        omega
      nlinarith [hL1Rpos, hsmall]
    calc (2 : ℝ) ^ k * (⌈X⌉₊ : ℝ)
        ≤ (2 : ℝ) ^ k * (2 * X) := by
          apply mul_le_mul_of_nonneg_left hceil (by positivity)
      _ = (2 : ℝ) ^ (2 - (k : ℤ)) * L1R := hq2X
      _ < L1R := hlt
  · -- (C6) dens_fiber_survival : 8h₂ < (1 − ε₂)/q₁
    -- 8 q₁ h₂ < 1 − ε₂.  8 q₁ h₂ ≤ 32k²·2^{−3ℓ} < 2^{7−ℓ} ≤ 1/2 (ℓ ≥ 8); 1−ε₂ ≥ 3/4.
    have hq1Rpos : (0 : ℝ) < (q1 (2 ^ k) : ℝ) := by
      have := hq1ge2; exact_mod_cast (by omega : 0 < q1 (2 ^ k))
    rw [lt_div_iff₀ hq1Rpos]
    -- h₂ ≤ 2^{−3ℓ}
    have hh2b : h2 (2 ^ k) ≤ (2 : ℝ) ^ (-(3 * Nat.log 2 (Nat.log 2 (2 ^ k)) : ℤ)) :=
      h2_le_pow (M := Nat.log 2 (Nat.log 2 (2 ^ k))) (le_refl _)
    set ℓ := Nat.log 2 (Nat.log 2 (2 ^ k)) with hℓdef
    -- q₁ ≤ 4k² and k < 2^{ℓ+1}
    have hq1R : (q1 (2 ^ k) : ℝ) ≤ 4 * (k : ℝ) ^ 2 := by
      have h := hq1le; exact_mod_cast h
    -- k < 2^{ℓ+1}  (ℓ = loglog(2^k) = log k, since loglog(2^k) = log k)
    have hℓeq : ℓ = Nat.log 2 k := by rw [hℓdef, hlogk]
    have hklt : (k : ℝ) < (2 : ℝ) ^ ((ℓ : ℤ) + 1) := by
      have hnat : k < 2 ^ (ℓ + 1) := by
        rw [hℓeq]; exact Nat.lt_pow_succ_log_self (b := 2) (by norm_num) k
      calc (k : ℝ) < ((2 ^ (ℓ + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = (2 : ℝ) ^ ((ℓ : ℤ) + 1) := by
            rw [show ((ℓ : ℤ) + 1) = ((ℓ + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
            push_cast; ring
    -- 8 q₁ h₂ ≤ 32 k² 2^{−3ℓ} < 32·2^{2ℓ+2}·2^{−3ℓ} = 2^{7−ℓ} ≤ 1/2
    have hℓ8 : (8 : ℤ) ≤ ℓ := by exact_mod_cast hloglog8
    have hk2 : (k : ℝ) ^ 2 < (2 : ℝ) ^ (2 * (ℓ : ℤ) + 2) := by
      have hkpos : (0 : ℝ) ≤ (k : ℝ) := by positivity
      have hsq : (k : ℝ) ^ 2 < ((2 : ℝ) ^ ((ℓ : ℤ) + 1)) ^ 2 := by
        apply pow_lt_pow_left₀ hklt hkpos (by norm_num)
      rw [← zpow_natCast ((2:ℝ) ^ ((ℓ : ℤ) + 1)) 2, ← zpow_mul] at hsq
      rw [show ((ℓ : ℤ) + 1) * (2 : ℕ) = 2 * (ℓ : ℤ) + 2 by push_cast; ring] at hsq
      exact hsq
    have hh2pos : 0 < h2 (2 ^ k) := h2_pos
    have hkey : 8 * (q1 (2 ^ k) : ℝ) * h2 (2 ^ k) < 1 / 2 := by
      -- 8 q₁ h₂ ≤ 8 q₁ · 2^{−3ℓ} ≤ 8·4k²·2^{−3ℓ} = 32 k² 2^{−3ℓ}
      have hstep1 : 8 * (q1 (2 ^ k) : ℝ) * h2 (2 ^ k)
          ≤ 8 * (q1 (2 ^ k) : ℝ) * (2 : ℝ) ^ (-(3 * ℓ : ℤ)) :=
        mul_le_mul_of_nonneg_left hh2b (by positivity)
      have hstep2 : 8 * (q1 (2 ^ k) : ℝ) * (2 : ℝ) ^ (-(3 * ℓ : ℤ))
          ≤ 32 * (k : ℝ) ^ 2 * (2 : ℝ) ^ (-(3 * ℓ : ℤ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [hq1R, hq1Rpos.le]
      have h32 : 8 * (q1 (2 ^ k) : ℝ) * h2 (2 ^ k)
          ≤ 32 * (k : ℝ) ^ 2 * (2 : ℝ) ^ (-(3 * ℓ : ℤ)) := le_trans hstep1 hstep2
      have hchain : 32 * (k : ℝ) ^ 2 * (2 : ℝ) ^ (-(3 * ℓ : ℤ)) < 1 / 2 := by
        have hprod : 32 * (k : ℝ) ^ 2 * (2 : ℝ) ^ (-(3 * ℓ : ℤ))
            < 32 * (2 : ℝ) ^ (2 * (ℓ : ℤ) + 2) * (2 : ℝ) ^ (-(3 * ℓ : ℤ)) := by
          apply mul_lt_mul_of_pos_right _ (by positivity)
          exact mul_lt_mul_of_pos_left hk2 (by norm_num)
        have hpow : 32 * (2 : ℝ) ^ (2 * (ℓ : ℤ) + 2) * (2 : ℝ) ^ (-(3 * ℓ : ℤ))
            = (2 : ℝ) ^ (7 - (ℓ : ℤ)) := by
          rw [show (32 : ℝ) = (2 : ℝ) ^ (5 : ℤ) by norm_num,
              mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
              ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          congr 1; ring
        rw [hpow] at hprod
        have hle : (2 : ℝ) ^ (7 - (ℓ : ℤ)) ≤ (2 : ℝ) ^ (-1 : ℤ) := by
          apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2); omega
        have hhalf : (2 : ℝ) ^ (-1 : ℤ) = 1 / 2 := by norm_num
        rw [hhalf] at hle
        linarith [hprod, hle]
      linarith [h32, hchain]
    have hε2small : epsQT (q2 (2 ^ k)) (t2 (2 ^ k)) ≤ 1 / 2 := le_trans hε2 (by norm_num)
    have halign : 8 * h2 (2 ^ k) * (q1 (2 ^ k) : ℝ)
        = 8 * (q1 (2 ^ k) : ℝ) * h2 (2 ^ k) := by ring
    rw [halign]
    linarith [hkey, hε2small]
  · -- (C7) dens_nondominant_slack : (q₂−1)(2^{−b₁+1}L₁+1) < η₂·L₁
    -- η₂·L₁ = q₂·2^{−b₁+1}·L₁ (def eta2); reduces to (q₂−1) < 2^{−b₁+1}·L₁.
    have hη2 : eta2 (2 ^ k) = (q2 (2 ^ k) : ℝ) * (2 : ℝ) ^ (-(b1 (2 ^ k) : ℤ) + 1) := rfl
    rw [hη2, hq2eq]
    set L1R := (L1 (2 ^ k) : ℝ) with hL1R
    have hL1Rpos : (0 : ℝ) < L1R := by rw [hL1R]; exact_mod_cast hL1pos
    set P := (2 : ℝ) ^ (-(b1 (2 ^ k) : ℤ) + 1) with hP
    have hPpos : (0 : ℝ) < P := by rw [hP]; positivity
    -- Need (q₂−1)(P·L₁+1) < q₂·P·L₁, i.e. (q₂−1) < P·L₁.
    have hPscale : P = (2 : ℝ) ^ (1 - 2 * (k : ℤ)) := by rw [hP, hb1]; congr 1; push_cast; ring
    have hPL1big : ((2 : ℝ) ^ k - 1) < P * L1R := by
      -- P·L₁ ≥ 2^{62k} > 2^k − 1
      have hfloor : (2 : ℝ) ^ ((64 * k : ℤ) - 1) ≤ L1R := by
        rw [hL1R]
        refine le_trans ?_ hL1floor
        rw [show (2 : ℝ) ^ (t1 (2 ^ k) - 1) = (2 : ℝ) ^ ((t1 (2 ^ k) : ℤ) - 1) by
          rw [← zpow_natCast]; congr 1; have := t1_pos (2 ^ k); omega]
        apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        have : (64 : ℤ) * k ≤ t1 (2 ^ k) := by exact_mod_cast ht1lo
        omega
      have hstep : P * (2 : ℝ) ^ ((64 * k : ℤ) - 1) = (2 : ℝ) ^ (62 * (k : ℤ)) := by
        rw [hPscale, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
      have hPL1ge : (2 : ℝ) ^ (62 * (k : ℤ)) ≤ P * L1R := by
        calc (2 : ℝ) ^ (62 * (k : ℤ)) = P * (2 : ℝ) ^ ((64 * k : ℤ) - 1) := hstep.symm
          _ ≤ P * L1R := mul_le_mul_of_nonneg_left hfloor hPpos.le
      have hbig : ((2 : ℝ) ^ k - 1) < (2 : ℝ) ^ (62 * (k : ℤ)) := by
        have h1 : (2 : ℝ) ^ k = (2 : ℝ) ^ (k : ℤ) := by rw [zpow_natCast]
        have h2 : (2 : ℝ) ^ (k : ℤ) < (2 : ℝ) ^ (62 * (k : ℤ)) := by
          apply zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2); omega
        rw [h1]; linarith
      linarith [hbig, hPL1ge]
    -- expand and conclude:  ↑(2^k) = (2:ℝ)^k, then (q₂−1) < P L₁ gives the slack.
    rw [show (((2 ^ k : ℕ)) : ℝ) = (2 : ℝ) ^ k from by push_cast; ring]
    nlinarith [hPL1big, hPpos, hL1Rpos]
  · -- (C8) dens_stage3_rowloss : 3⌈2^{−b₂+1}·L₂⌉ ≤ 8h₂·L₂
    -- 2^{−b₂+1} = 2h₂; ⌈2h₂L₂⌉ ≤ 2h₂L₂+1; 2h₂L₂ ≥ 3 (from t₂ ≥ 3ℓ+2), so 6h₂L₂+3 ≤ 8h₂L₂.
    set L2R := (L2 (2 ^ k) : ℝ) with hL2R
    have hL2Rpos : (0 : ℝ) < L2R := by rw [hL2R]; exact_mod_cast hL2pos
    have hh2e : h2 (2 ^ k) = (2 : ℝ) ^ (-(3 * Nat.log 2 (Nat.log 2 (2 ^ k)) : ℤ)) := h2_eq
    set ℓ := Nat.log 2 (Nat.log 2 (2 ^ k)) with hℓdef
    have hh2pos : 0 < h2 (2 ^ k) := h2_pos
    -- 2^{−b₂+1} = 2·h₂
    have hscale : (2 : ℝ) ^ (-(b2 (2 ^ k) : ℤ) + 1) = 2 * h2 (2 ^ k) := by
      rw [hh2e]
      have hb2 : b2 (2 ^ k) = 3 * ℓ := by rw [hℓdef, b2]
      rw [hb2, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]; push_cast; ring
    rw [hscale]
    -- 2·h₂·L₂ ≥ 3:  L₂ ≥ q₁^{t₂−1} ≥ 2^{t₂−1}, h₂ = 2^{−3ℓ}, t₂ ≥ 3ℓ+2.
    have ht2ge : 3 * ℓ + 2 ≤ t2 (2 ^ k) := by
      have := Params.t2_ge (d := 2 ^ k) hlog256; rwa [← hℓdef] at this
    have hL2ge2 : (2 : ℝ) ^ (t2 (2 ^ k) - 1) ≤ L2R := by
      rw [hL2R]
      refine le_trans ?_ hL2floor
      exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hq1ge2) _
    have hge3 : (3 : ℝ) ≤ 2 * h2 (2 ^ k) * L2R := by
      have hpm : 2 * h2 (2 ^ k) * (2 : ℝ) ^ (t2 (2 ^ k) - 1)
          = (2 : ℝ) ^ ((t2 (2 ^ k) : ℤ) - 3 * ℓ) := by
        rw [hh2e]
        have e1 : (2 : ℝ) ^ (t2 (2 ^ k) - 1) = (2 : ℝ) ^ (((t2 (2 ^ k) - 1 : ℕ)) : ℤ) := by
          rw [zpow_natCast]
        rw [e1, show (2 : ℝ) * (2 : ℝ) ^ (-(3 * ℓ : ℤ)) * (2 : ℝ) ^ (((t2 (2 ^ k) - 1 : ℕ)) : ℤ)
              = (2 : ℝ) ^ (1 : ℤ) * (2 : ℝ) ^ (-(3 * ℓ : ℤ))
                  * (2 : ℝ) ^ (((t2 (2 ^ k) - 1 : ℕ)) : ℤ) by rw [zpow_one]]
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 1
        have : ((t2 (2 ^ k) - 1 : ℕ) : ℤ) = (t2 (2 ^ k) : ℤ) - 1 := by
          have := t2_pos (2 ^ k); omega
        rw [this]; ring
      have hexp : (2 : ℝ) ^ (2 : ℤ) ≤ (2 : ℝ) ^ ((t2 (2 ^ k) : ℤ) - 3 * ℓ) := by
        apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        have : (3 : ℤ) * ℓ + 2 ≤ t2 (2 ^ k) := by exact_mod_cast ht2ge
        omega
      have h4 : (2 : ℝ) ^ (2 : ℤ) = 4 := by norm_num
      have hmul : 2 * h2 (2 ^ k) * (2 : ℝ) ^ (t2 (2 ^ k) - 1) ≤ 2 * h2 (2 ^ k) * L2R :=
        mul_le_mul_of_nonneg_left hL2ge2 (by positivity)
      calc (3 : ℝ) ≤ 4 := by norm_num
        _ = (2 : ℝ) ^ (2 : ℤ) := h4.symm
        _ ≤ (2 : ℝ) ^ ((t2 (2 ^ k) : ℤ) - 3 * ℓ) := hexp
        _ = 2 * h2 (2 ^ k) * (2 : ℝ) ^ (t2 (2 ^ k) - 1) := hpm.symm
        _ ≤ 2 * h2 (2 ^ k) * L2R := hmul
    -- ⌈2h₂L₂⌉ ≤ 2h₂L₂ + 1
    have hceil : (⌈2 * h2 (2 ^ k) * L2R⌉₊ : ℝ) ≤ 2 * h2 (2 ^ k) * L2R + 1 := by
      have := Nat.ceil_lt_add_one (a := 2 * h2 (2 ^ k) * L2R) (by positivity); linarith
    nlinarith [hceil, hge3]
-- CLAIM-END lem:large-d-checklist

-- CLAIM-BEGIN aux:large-d-checklist-2p18
set_option maxHeartbeats 1600000 in
/-- **`aux:large-d-checklist-2p18`**: the checklist core with the threshold
written as a logarithmic hypothesis. This extracts the proof body of
`large_d_checklist`; the old existential witness is opaque through `.choose`, so
the reusable statement is the monotone `log d >= 256` form. -/
theorem checklist_of_log_ge_256 {d : Nat} (hpow : IsPow2 d)
    (hlog : 256 <= Nat.log 2 d) : Checklist d := by
  obtain ⟨k, rfl⟩ := hpow
  have hlogk : Nat.log 2 (2 ^ k) = k := log_two_pow k
  have hk : 256 <= k := by
    rw [hlogk] at hlog
    exact hlog
  have hlog256 : 256 ≤ Nat.log 2 (2 ^ k) := by rw [hlogk]; exact hk
  have hlog64 : 64 ≤ Nat.log 2 (2 ^ k) := by omega
  have hlog2 : 2 ≤ Nat.log 2 (2 ^ k) := by omega
  have hlog6 : 6 ≤ Nat.log 2 (2 ^ k) := by omega
  have hloglog : 1 ≤ Nat.log 2 (Nat.log 2 (2 ^ k)) :=
    Params.loglog_pos hlog2
  -- loglog (2^k) = log k ≥ log 256 = 8 (since k ≥ 256)
  have hloglog8 : 8 ≤ Nat.log 2 (Nat.log 2 (2 ^ k)) := by
    rw [hlogk]
    calc 8 = Nat.log 2 256 := by norm_num [Nat.log]
      _ ≤ Nat.log 2 k := Nat.log_mono_right hk
  have hloglog6 : 6 ≤ Nat.log 2 (Nat.log 2 (2 ^ k)) := by omega
  have hpow2 : IsPow2 (2 ^ k) := ⟨k, rfl⟩
  -- accuracy handles: ε₂ ≤ 1/4 (n = 2 ≤ q₂·t₂), ε₁ ≤ 1/4.
  have hq2t2 : (2 : ℕ) ≤ q2 (2 ^ k) * t2 (2 ^ k) := by
    have : 2 ≤ q2 (2 ^ k) := by
      rw [q2_eq_self rfl]; exact Nat.one_lt_two_pow (by omega)
    have ht2 : 1 ≤ t2 (2 ^ k) := t2_pos _
    calc 2 ≤ q2 (2 ^ k) := this
      _ = q2 (2 ^ k) * 1 := (Nat.mul_one _).symm
      _ ≤ q2 (2 ^ k) * t2 (2 ^ k) := by gcongr
  have hε2 : epsQT (q2 (2 ^ k)) (t2 (2 ^ k)) ≤ 1 / 4 := by
    have := epsQT_le_inv_mul (q2_pos _) (t2_pos _) hq2t2 (by norm_num)
    simpa using this.trans (by norm_num)
  have hε2pos : 0 < epsQT (q2 (2 ^ k)) (t2 (2 ^ k)) :=
    epsQT_pos (q2_pos _) (t2_pos _)
  -- ε₁ = epsQT (2^a+3) t1 ≤ 1/4
  have hε1n : (2 : ℕ) ≤ (2 ^ a (2 ^ k) + 3) * t1 (2 ^ k) := by
    have : 1 ≤ t1 (2 ^ k) := t1_pos _
    nlinarith [Nat.one_le_iff_ne_zero.mpr (by positivity : (2:ℕ) ^ a (2^k) ≠ 0)]
  have hε1 : epsQT (2 ^ a (2 ^ k) + 3) (t1 (2 ^ k)) ≤ 1 / 4 := by
    have := epsQT_le_inv_mul (q := 2 ^ a (2 ^ k) + 3) (t := t1 (2 ^ k))
      (by positivity) (t1_pos _) hε1n (by norm_num)
    simpa using this.trans (by norm_num)
  have hε1pos : 0 < epsQT (2 ^ a (2 ^ k) + 3) (t1 (2 ^ k)) :=
    epsQT_pos (by positivity) (t1_pos _)
  -- `8 h₂ ≤ 1/32`
  have hh2 : 8 * h2 (2 ^ k) ≤ 1 / 32 := by
    have hb := h2_le_pow (M := 6) hloglog6
    have hval : (2 : ℝ) ^ (-(3 * (6 : ℕ) : ℤ)) = 1 / 262144 := by norm_num
    rw [hval] at hb
    nlinarith [h2_pos (d := 2 ^ k)]
  -- Shared handles for the App C.1 density/count fields (C5–C8).
  -- `b₁ = 2k`, `t₁ ≥ 64k`, `q₂ = 2^k`, `2 ≤ q₁ ≤ 4k²`, and the size floors.
  have hb1 : b1 (2 ^ k) = 2 * k := by unfold b1; rw [hlogk]
  have ht1lo : 64 * k ≤ t1 (2 ^ k) := by
    have := (Params.t1_bracket (d := 2 ^ k) (by omega)).1; rwa [hlogk] at this
  have hq2eq : q2 (2 ^ k) = 2 ^ k := q2_eq_self rfl
  have hq1ge2 : 2 ≤ q1 (2 ^ k) := by
    have := Params.le_q1_add_two (d := 2 ^ k) (by omega); rw [hlogk] at this; nlinarith
  have hq1le : q1 (2 ^ k) ≤ 4 * k ^ 2 := by
    have := Params.q1_le (d := 2 ^ k) (by omega); rwa [hlogk] at this
  -- size floors  |C₁| ≥ 2^{t₁-1}  and  |C₂| ≥ q₁^{t₂-1}
  have hL1floor : ((2 : ℝ) ^ (t1 (2 ^ k) - 1)) ≤ (L1 (2 ^ k) : ℝ) :=
    L1_ge_pow _ (Params.t1_le_q1_add_five hlog64)
  have hL2floor : ((q1 (2 ^ k) : ℝ) ^ (t2 (2 ^ k) - 1)) ≤ (L2 (2 ^ k) : ℝ) :=
    L2_ge_pow _ (Params.t2_le_q2 hpow2 hlog6) hq1ge2
  have hL1pos : 0 < L1 (2 ^ k) := L1_pos _ (Params.t1_le_q1_add_five hlog64)
  have hL2pos : 0 < L2 (2 ^ k) := L2_pos _ (Params.t2_le_q2 hpow2 hlog6) (by omega)
  refine
    { t1_le_q1_add_five := Params.t1_le_q1_add_five hlog64
      one_le_q1 := Params.one_le_q1 hlog2
      t2_le_q2 := Params.t2_le_q2 hpow2 hlog6
      t2_le_pow_b1 := Params.t2_le_pow_b1 hlog6
      q1_add_two_eq := Params.q1_add_two_eq_r1_mul_t1 hlog64
      q2_eq := Params.q2_eq_r2_mul_t2 hpow2 hlog6
      clog_q2_eq := Params.clog_q2_eq_log_q2 hpow2
      q2_eq_self := q2_eq_self rfl
      loglog_pos := hloglog
      a_ge_two := ?_
      L1_ge := L1_ge_pow _ (Params.t1_le_q1_add_five hlog64)
      L2_ge := L2_ge_pow _ (Params.t2_le_q2 hpow2 hlog6) ?_
      dens_sep := ?_
      dens_sep_dense := ?_
      dens_eta_lt := ?_
      dens_survive := ?_
      dens_dominant_count := ?_
      dens_fiber_survival := ?_
      dens_nondominant_slack := ?_
      dens_stage3_rowloss := ?_
      seed_slack := Params.seed_slack hlog64 }
  · -- a ≥ 2 : 2^a = q1+2 ≥ 2 log²d ≥ 2·64² ≥ 2^13, so a ≥ 13 ≥ 2
    have h2a : q1 (2 ^ k) + 2 = 2 ^ a (2 ^ k) := Params.q1_add_two_pow (by omega)
    have hlow : 2 * Nat.log 2 (2 ^ k) ^ 2 ≤ q1 (2 ^ k) + 2 :=
      Params.le_q1_add_two (by omega)
    rw [h2a] at hlow
    rw [hlogk] at hlow
    have hbig : (2 : ℕ) ^ 2 ≤ 2 ^ a (2 ^ k) := by
      calc (2 : ℕ) ^ 2 = 4 := by norm_num
        _ ≤ 2 * k ^ 2 := by nlinarith
        _ ≤ 2 ^ a (2 ^ k) := hlow
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hbig
  · -- 2 ≤ q1 for L2
    have := Params.le_q1_add_two (d := 2 ^ k) (by omega)
    rw [hlogk] at this
    nlinarith
  · -- dens_sep : 0.72 ≤ 1/(1+ε₂)
    have : 2 * (1 / 2 + delta) ^ 2 = 0.72 := by unfold delta; norm_num
    rw [this]
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  · -- dens_sep_dense
    intro σ hσ
    have hσlb : (0.95 : ℝ) ≤ σ := by
      have : (1 : ℝ) - 8 * h2 (2 ^ k) ≤ σ := hσ
      linarith
    have hval : 2 * (1 / 2 + delta) ^ 2 = 0.72 := by unfold delta; norm_num
    rw [hval, le_div_iff₀ (by linarith)]
    nlinarith
  · -- dens_eta_lt : η₂ < (1-ε₁)/2
    have hη : eta2 (2 ^ k) ≤ (2 : ℝ) ^ (-(2 : ℤ)) := by
      have := Params.eta2_le_pow (d := 2 ^ k) hpow2 (N := 2) (by rw [hlogk]; omega)
      simpa using this
    have hηval : (2 : ℝ) ^ (-(2 : ℤ)) = 1 / 4 := by norm_num
    rw [hηval] at hη
    rw [lt_div_iff₀ (by norm_num)]
    nlinarith
  · -- dens_survive : 2^{-(b1+log r2)} ≤ 1 - η₂
    have hη : eta2 (2 ^ k) ≤ 1 / 2 := Params.eta2_le_half hpow2 hlog2
    have hlhs : (2 : ℝ) ^ (-((b1 (2 ^ k) : ℤ) + Nat.log 2 (r2 (2 ^ k)))) ≤ 1 / 2 := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℤ) by norm_num]
      apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      have hb1' : 1 ≤ b1 (2 ^ k) := by
        unfold b1; rw [hlogk]; omega
      omega
    linarith
  · -- (C5) dens_dominant_count : q₂·⌈2^{−b₁+1}·L₁⌉ < L₁
    -- X := 2^{1−2k}·L₁ ≥ 2^{62k} ≥ 1, ⌈X⌉ ≤ 2X, q₂·2X = 2^{2−k}·L₁ < L₁.
    set L1R := (L1 (2 ^ k) : ℝ) with hL1R
    have hL1Rpos : (0 : ℝ) < L1R := by rw [hL1R]; exact_mod_cast hL1pos
    -- 2^{−b₁+1} = 2^{1−2k} (real zpow)
    have hscale : (2 : ℝ) ^ (-(b1 (2 ^ k) : ℤ) + 1) = (2 : ℝ) ^ (1 - 2 * (k : ℤ)) := by
      rw [hb1]; congr 1; push_cast; ring
    rw [hscale, hq2eq, show (((2 ^ k : ℕ) : ℝ)) = (2 : ℝ) ^ k from by push_cast; ring]
    set X := (2 : ℝ) ^ (1 - 2 * (k : ℤ)) * L1R with hX
    -- L₁ ≥ 2^{t₁−1} ≥ 2^{64k−1}, so X ≥ 2^{1−2k}·2^{64k−1} = 2^{62k} ≥ 1.
    have hpowcast : (2 : ℝ) ^ (t1 (2 ^ k) - 1) = (2 : ℝ) ^ ((t1 (2 ^ k) : ℤ) - 1) := by
      rw [← zpow_natCast]; congr 1; have := t1_pos (2 ^ k); omega
    have hXge1 : (1 : ℝ) ≤ X := by
      have hfloor : (2 : ℝ) ^ ((64 * k : ℤ) - 1) ≤ L1R := by
        rw [hL1R]
        refine le_trans ?_ hL1floor
        rw [hpowcast]
        apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        have : (64 : ℤ) * k ≤ t1 (2 ^ k) := by exact_mod_cast ht1lo
        omega
      have hstep : (2 : ℝ) ^ (1 - 2 * (k : ℤ)) * (2 : ℝ) ^ ((64 * k : ℤ) - 1)
          = (2 : ℝ) ^ (62 * (k : ℤ)) := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
      have hbig : (1 : ℝ) ≤ (2 : ℝ) ^ (62 * (k : ℤ)) := by
        apply one_le_zpow₀ (by norm_num : (1 : ℝ) ≤ 2); positivity
      calc (1 : ℝ) ≤ (2 : ℝ) ^ (62 * (k : ℤ)) := hbig
        _ = (2 : ℝ) ^ (1 - 2 * (k : ℤ)) * (2 : ℝ) ^ ((64 * k : ℤ) - 1) := hstep.symm
        _ ≤ (2 : ℝ) ^ (1 - 2 * (k : ℤ)) * L1R := by
            apply mul_le_mul_of_nonneg_left hfloor (by positivity)
    -- ⌈X⌉ ≤ X + 1 ≤ 2X
    have hceil : (⌈X⌉₊ : ℝ) ≤ 2 * X := by
      have h1 : (⌈X⌉₊ : ℝ) < X + 1 := Nat.ceil_lt_add_one (by linarith)
      linarith
    -- 2^k · 2X = 2^{2−k}·L₁ < L₁
    have hq2X : (2 : ℝ) ^ k * (2 * X) = (2 : ℝ) ^ (2 - (k : ℤ)) * L1R := by
      rw [hX]
      have hkcast : (2 : ℝ) ^ k = (2 : ℝ) ^ (k : ℤ) := by rw [zpow_natCast]
      rw [hkcast, show (2 : ℝ) * ((2 : ℝ) ^ (1 - 2 * (k : ℤ)) * L1R)
            = (2 : ℝ) ^ (1 : ℤ) * (2 : ℝ) ^ (1 - 2 * (k : ℤ)) * L1R by
          rw [zpow_one]; ring]
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
          ← mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 2; ring
    have hlt : (2 : ℝ) ^ (2 - (k : ℤ)) * L1R < L1R := by
      have hsmall : (2 : ℝ) ^ (2 - (k : ℤ)) < 1 := by
        rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℤ) by norm_num]
        apply zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2)
        omega
      nlinarith [hL1Rpos, hsmall]
    calc (2 : ℝ) ^ k * (⌈X⌉₊ : ℝ)
        ≤ (2 : ℝ) ^ k * (2 * X) := by
          apply mul_le_mul_of_nonneg_left hceil (by positivity)
      _ = (2 : ℝ) ^ (2 - (k : ℤ)) * L1R := hq2X
      _ < L1R := hlt
  · -- (C6) dens_fiber_survival : 8h₂ < (1 − ε₂)/q₁
    -- 8 q₁ h₂ < 1 − ε₂.  8 q₁ h₂ ≤ 32k²·2^{−3ℓ} < 2^{7−ℓ} ≤ 1/2 (ℓ ≥ 8); 1−ε₂ ≥ 3/4.
    have hq1Rpos : (0 : ℝ) < (q1 (2 ^ k) : ℝ) := by
      have := hq1ge2; exact_mod_cast (by omega : 0 < q1 (2 ^ k))
    rw [lt_div_iff₀ hq1Rpos]
    -- h₂ ≤ 2^{−3ℓ}
    have hh2b : h2 (2 ^ k) ≤ (2 : ℝ) ^ (-(3 * Nat.log 2 (Nat.log 2 (2 ^ k)) : ℤ)) :=
      h2_le_pow (M := Nat.log 2 (Nat.log 2 (2 ^ k))) (le_refl _)
    set ℓ := Nat.log 2 (Nat.log 2 (2 ^ k)) with hℓdef
    -- q₁ ≤ 4k² and k < 2^{ℓ+1}
    have hq1R : (q1 (2 ^ k) : ℝ) ≤ 4 * (k : ℝ) ^ 2 := by
      have h := hq1le; exact_mod_cast h
    -- k < 2^{ℓ+1}  (ℓ = loglog(2^k) = log k, since loglog(2^k) = log k)
    have hℓeq : ℓ = Nat.log 2 k := by rw [hℓdef, hlogk]
    have hklt : (k : ℝ) < (2 : ℝ) ^ ((ℓ : ℤ) + 1) := by
      have hnat : k < 2 ^ (ℓ + 1) := by
        rw [hℓeq]; exact Nat.lt_pow_succ_log_self (b := 2) (by norm_num) k
      calc (k : ℝ) < ((2 ^ (ℓ + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = (2 : ℝ) ^ ((ℓ : ℤ) + 1) := by
            rw [show ((ℓ : ℤ) + 1) = ((ℓ + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
            push_cast; ring
    -- 8 q₁ h₂ ≤ 32 k² 2^{−3ℓ} < 32·2^{2ℓ+2}·2^{−3ℓ} = 2^{7−ℓ} ≤ 1/2
    have hℓ8 : (8 : ℤ) ≤ ℓ := by exact_mod_cast hloglog8
    have hk2 : (k : ℝ) ^ 2 < (2 : ℝ) ^ (2 * (ℓ : ℤ) + 2) := by
      have hkpos : (0 : ℝ) ≤ (k : ℝ) := by positivity
      have hsq : (k : ℝ) ^ 2 < ((2 : ℝ) ^ ((ℓ : ℤ) + 1)) ^ 2 := by
        apply pow_lt_pow_left₀ hklt hkpos (by norm_num)
      rw [← zpow_natCast ((2:ℝ) ^ ((ℓ : ℤ) + 1)) 2, ← zpow_mul] at hsq
      rw [show ((ℓ : ℤ) + 1) * (2 : ℕ) = 2 * (ℓ : ℤ) + 2 by push_cast; ring] at hsq
      exact hsq
    have hh2pos : 0 < h2 (2 ^ k) := h2_pos
    have hkey : 8 * (q1 (2 ^ k) : ℝ) * h2 (2 ^ k) < 1 / 2 := by
      -- 8 q₁ h₂ ≤ 8 q₁ · 2^{−3ℓ} ≤ 8·4k²·2^{−3ℓ} = 32 k² 2^{−3ℓ}
      have hstep1 : 8 * (q1 (2 ^ k) : ℝ) * h2 (2 ^ k)
          ≤ 8 * (q1 (2 ^ k) : ℝ) * (2 : ℝ) ^ (-(3 * ℓ : ℤ)) :=
        mul_le_mul_of_nonneg_left hh2b (by positivity)
      have hstep2 : 8 * (q1 (2 ^ k) : ℝ) * (2 : ℝ) ^ (-(3 * ℓ : ℤ))
          ≤ 32 * (k : ℝ) ^ 2 * (2 : ℝ) ^ (-(3 * ℓ : ℤ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [hq1R, hq1Rpos.le]
      have h32 : 8 * (q1 (2 ^ k) : ℝ) * h2 (2 ^ k)
          ≤ 32 * (k : ℝ) ^ 2 * (2 : ℝ) ^ (-(3 * ℓ : ℤ)) := le_trans hstep1 hstep2
      have hchain : 32 * (k : ℝ) ^ 2 * (2 : ℝ) ^ (-(3 * ℓ : ℤ)) < 1 / 2 := by
        have hprod : 32 * (k : ℝ) ^ 2 * (2 : ℝ) ^ (-(3 * ℓ : ℤ))
            < 32 * (2 : ℝ) ^ (2 * (ℓ : ℤ) + 2) * (2 : ℝ) ^ (-(3 * ℓ : ℤ)) := by
          apply mul_lt_mul_of_pos_right _ (by positivity)
          exact mul_lt_mul_of_pos_left hk2 (by norm_num)
        have hpow : 32 * (2 : ℝ) ^ (2 * (ℓ : ℤ) + 2) * (2 : ℝ) ^ (-(3 * ℓ : ℤ))
            = (2 : ℝ) ^ (7 - (ℓ : ℤ)) := by
          rw [show (32 : ℝ) = (2 : ℝ) ^ (5 : ℤ) by norm_num,
              mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
              ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          congr 1; ring
        rw [hpow] at hprod
        have hle : (2 : ℝ) ^ (7 - (ℓ : ℤ)) ≤ (2 : ℝ) ^ (-1 : ℤ) := by
          apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2); omega
        have hhalf : (2 : ℝ) ^ (-1 : ℤ) = 1 / 2 := by norm_num
        rw [hhalf] at hle
        linarith [hprod, hle]
      linarith [h32, hchain]
    have hε2small : epsQT (q2 (2 ^ k)) (t2 (2 ^ k)) ≤ 1 / 2 := le_trans hε2 (by norm_num)
    have halign : 8 * h2 (2 ^ k) * (q1 (2 ^ k) : ℝ)
        = 8 * (q1 (2 ^ k) : ℝ) * h2 (2 ^ k) := by ring
    rw [halign]
    linarith [hkey, hε2small]
  · -- (C7) dens_nondominant_slack : (q₂−1)(2^{−b₁+1}L₁+1) < η₂·L₁
    -- η₂·L₁ = q₂·2^{−b₁+1}·L₁ (def eta2); reduces to (q₂−1) < 2^{−b₁+1}·L₁.
    have hη2 : eta2 (2 ^ k) = (q2 (2 ^ k) : ℝ) * (2 : ℝ) ^ (-(b1 (2 ^ k) : ℤ) + 1) := rfl
    rw [hη2, hq2eq]
    set L1R := (L1 (2 ^ k) : ℝ) with hL1R
    have hL1Rpos : (0 : ℝ) < L1R := by rw [hL1R]; exact_mod_cast hL1pos
    set P := (2 : ℝ) ^ (-(b1 (2 ^ k) : ℤ) + 1) with hP
    have hPpos : (0 : ℝ) < P := by rw [hP]; positivity
    -- Need (q₂−1)(P·L₁+1) < q₂·P·L₁, i.e. (q₂−1) < P·L₁.
    have hPscale : P = (2 : ℝ) ^ (1 - 2 * (k : ℤ)) := by rw [hP, hb1]; congr 1; push_cast; ring
    have hPL1big : ((2 : ℝ) ^ k - 1) < P * L1R := by
      -- P·L₁ ≥ 2^{62k} > 2^k − 1
      have hfloor : (2 : ℝ) ^ ((64 * k : ℤ) - 1) ≤ L1R := by
        rw [hL1R]
        refine le_trans ?_ hL1floor
        rw [show (2 : ℝ) ^ (t1 (2 ^ k) - 1) = (2 : ℝ) ^ ((t1 (2 ^ k) : ℤ) - 1) by
          rw [← zpow_natCast]; congr 1; have := t1_pos (2 ^ k); omega]
        apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        have : (64 : ℤ) * k ≤ t1 (2 ^ k) := by exact_mod_cast ht1lo
        omega
      have hstep : P * (2 : ℝ) ^ ((64 * k : ℤ) - 1) = (2 : ℝ) ^ (62 * (k : ℤ)) := by
        rw [hPscale, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
      have hPL1ge : (2 : ℝ) ^ (62 * (k : ℤ)) ≤ P * L1R := by
        calc (2 : ℝ) ^ (62 * (k : ℤ)) = P * (2 : ℝ) ^ ((64 * k : ℤ) - 1) := hstep.symm
          _ ≤ P * L1R := mul_le_mul_of_nonneg_left hfloor hPpos.le
      have hbig : ((2 : ℝ) ^ k - 1) < (2 : ℝ) ^ (62 * (k : ℤ)) := by
        have h1 : (2 : ℝ) ^ k = (2 : ℝ) ^ (k : ℤ) := by rw [zpow_natCast]
        have h2 : (2 : ℝ) ^ (k : ℤ) < (2 : ℝ) ^ (62 * (k : ℤ)) := by
          apply zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2); omega
        rw [h1]; linarith
      linarith [hbig, hPL1ge]
    -- expand and conclude:  ↑(2^k) = (2:ℝ)^k, then (q₂−1) < P L₁ gives the slack.
    rw [show (((2 ^ k : ℕ)) : ℝ) = (2 : ℝ) ^ k from by push_cast; ring]
    nlinarith [hPL1big, hPpos, hL1Rpos]
  · -- (C8) dens_stage3_rowloss : 3⌈2^{−b₂+1}·L₂⌉ ≤ 8h₂·L₂
    -- 2^{−b₂+1} = 2h₂; ⌈2h₂L₂⌉ ≤ 2h₂L₂+1; 2h₂L₂ ≥ 3 (from t₂ ≥ 3ℓ+2), so 6h₂L₂+3 ≤ 8h₂L₂.
    set L2R := (L2 (2 ^ k) : ℝ) with hL2R
    have hL2Rpos : (0 : ℝ) < L2R := by rw [hL2R]; exact_mod_cast hL2pos
    have hh2e : h2 (2 ^ k) = (2 : ℝ) ^ (-(3 * Nat.log 2 (Nat.log 2 (2 ^ k)) : ℤ)) := h2_eq
    set ℓ := Nat.log 2 (Nat.log 2 (2 ^ k)) with hℓdef
    have hh2pos : 0 < h2 (2 ^ k) := h2_pos
    -- 2^{−b₂+1} = 2·h₂
    have hscale : (2 : ℝ) ^ (-(b2 (2 ^ k) : ℤ) + 1) = 2 * h2 (2 ^ k) := by
      rw [hh2e]
      have hb2 : b2 (2 ^ k) = 3 * ℓ := by rw [hℓdef, b2]
      rw [hb2, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]; push_cast; ring
    rw [hscale]
    -- 2·h₂·L₂ ≥ 3:  L₂ ≥ q₁^{t₂−1} ≥ 2^{t₂−1}, h₂ = 2^{−3ℓ}, t₂ ≥ 3ℓ+2.
    have ht2ge : 3 * ℓ + 2 ≤ t2 (2 ^ k) := by
      have := Params.t2_ge (d := 2 ^ k) hlog256; rwa [← hℓdef] at this
    have hL2ge2 : (2 : ℝ) ^ (t2 (2 ^ k) - 1) ≤ L2R := by
      rw [hL2R]
      refine le_trans ?_ hL2floor
      exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hq1ge2) _
    have hge3 : (3 : ℝ) ≤ 2 * h2 (2 ^ k) * L2R := by
      have hpm : 2 * h2 (2 ^ k) * (2 : ℝ) ^ (t2 (2 ^ k) - 1)
          = (2 : ℝ) ^ ((t2 (2 ^ k) : ℤ) - 3 * ℓ) := by
        rw [hh2e]
        have e1 : (2 : ℝ) ^ (t2 (2 ^ k) - 1) = (2 : ℝ) ^ (((t2 (2 ^ k) - 1 : ℕ)) : ℤ) := by
          rw [zpow_natCast]
        rw [e1, show (2 : ℝ) * (2 : ℝ) ^ (-(3 * ℓ : ℤ)) * (2 : ℝ) ^ (((t2 (2 ^ k) - 1 : ℕ)) : ℤ)
              = (2 : ℝ) ^ (1 : ℤ) * (2 : ℝ) ^ (-(3 * ℓ : ℤ))
                  * (2 : ℝ) ^ (((t2 (2 ^ k) - 1 : ℕ)) : ℤ) by rw [zpow_one]]
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 1
        have : ((t2 (2 ^ k) - 1 : ℕ) : ℤ) = (t2 (2 ^ k) : ℤ) - 1 := by
          have := t2_pos (2 ^ k); omega
        rw [this]; ring
      have hexp : (2 : ℝ) ^ (2 : ℤ) ≤ (2 : ℝ) ^ ((t2 (2 ^ k) : ℤ) - 3 * ℓ) := by
        apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        have : (3 : ℤ) * ℓ + 2 ≤ t2 (2 ^ k) := by exact_mod_cast ht2ge
        omega
      have h4 : (2 : ℝ) ^ (2 : ℤ) = 4 := by norm_num
      have hmul : 2 * h2 (2 ^ k) * (2 : ℝ) ^ (t2 (2 ^ k) - 1) ≤ 2 * h2 (2 ^ k) * L2R :=
        mul_le_mul_of_nonneg_left hL2ge2 (by positivity)
      calc (3 : ℝ) ≤ 4 := by norm_num
        _ = (2 : ℝ) ^ (2 : ℤ) := h4.symm
        _ ≤ (2 : ℝ) ^ ((t2 (2 ^ k) : ℤ) - 3 * ℓ) := hexp
        _ = 2 * h2 (2 ^ k) * (2 : ℝ) ^ (t2 (2 ^ k) - 1) := hpm.symm
        _ ≤ 2 * h2 (2 ^ k) * L2R := hmul
    -- ⌈2h₂L₂⌉ ≤ 2h₂L₂ + 1
    have hceil : (⌈2 * h2 (2 ^ k) * L2R⌉₊ : ℝ) ≤ 2 * h2 (2 ^ k) * L2R + 1 := by
      have := Nat.ceil_lt_add_one (a := 2 * h2 (2 ^ k) * L2R) (by positivity); linarith
    nlinarith [hceil, hge3]

/-- Strong large-`d` checklist: the witness also forces the terminal-discharge
logarithmic gate `2^18 <= Nat.log 2 d`. The witness is kept symbolic as
`2 ^ (2 ^ 18)`; the proof only compares powers and never evaluates it. -/
theorem large_d_checklist_strong :
    exists d0 : Nat, forall d : Nat, IsPow2 d -> d0 <= d ->
      Checklist d /\ 2 ^ 18 <= Nat.log 2 d := by
  refine ⟨2 ^ (2 ^ 18), ?_⟩
  intro d hpow hge
  obtain ⟨k, rfl⟩ := hpow
  have hk2p18 : 2 ^ 18 <= k := by
    by_contra hlt
    have hlt' : k < 2 ^ 18 := by omega
    have hpowlt : (2 : Nat) ^ k < 2 ^ (2 ^ 18) :=
      Nat.pow_lt_pow_right (by norm_num) hlt'
    omega
  have hlog2p18 : 2 ^ 18 <= Nat.log 2 (2 ^ k) := by
    rw [log_two_pow]
    exact hk2p18
  have hlog256 : 256 <= Nat.log 2 (2 ^ k) :=
    le_trans (by norm_num : (256 : Nat) <= 2 ^ 18) hlog2p18
  exact ⟨checklist_of_log_ge_256 ⟨k, rfl⟩ hlog256, hlog2p18⟩
-- CLAIM-END aux:large-d-checklist-2p18

/-! ## `d_star` — the threshold constant (unregistered companion, D3)

Extracted from the checklist bundle by `Classical.choice` ONLY AFTER
`large_d_checklist` has exhibited the explicit power-of-two witness above
(the D3 ordering: the `Nonempty` obligation is discharged first). Downstream
`normalizeInstance` will be instantiated at `dstar := d_star`. -/

/-- The reduction's large-`d` threshold: a witness `d₀` from
`large_d_checklist`. -/
noncomputable def dStar : ℕ := large_d_checklist.choose

/-- Every power of two `≥ dStar` satisfies the full checklist bundle. -/
theorem checklist_of_dStar_le {d : ℕ} (hpow : IsPow2 d) (hge : dStar ≤ d) :
    Checklist d :=
  large_d_checklist.choose_spec d hpow hge

end NPCC
