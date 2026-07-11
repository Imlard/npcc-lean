import Mathlib
import NPCC.Stage2

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace NPCC

open Workspace.Types.CommComplexity

private theorem ctor_r2_eq_two_pow_log {d : Nat} (hpow : IsPow2 d)
    (hchk : Checklist d) :
    Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d) := by
  cases hpow with
  | intro k hk =>
      have hprod : Params.r2 d * Params.t2 d = 2 ^ k := by
        calc
          Params.r2 d * Params.t2 d = Params.q2 d := hchk.q2_eq.symm
          _ = d := hchk.q2_eq_self
          _ = 2 ^ k := hk
      have hr2_dvd : Dvd.dvd (Params.r2 d) (2 ^ k) :=
        Exists.intro (Params.t2 d) hprod.symm
      cases (Nat.dvd_prime_pow Nat.prime_two).mp hr2_dvd with
      | intro j hj_rest =>
          cases hj_rest with
          | intro _hj hr2pow =>
              rw [hr2pow, log_two_pow]

-- CLAIM-BEGIN aux:gate-discharge-partial

noncomputable def gateHardSeedM0 : Nat :=
  Classical.choose
    (hard_seed.{0} Params.jSurplus (by norm_num [Params.jSurplus])
      Params.delta (by norm_num [Params.delta])
      (by norm_num [Params.delta]))

noncomputable def gateHardSeedThreshold : Nat :=
  2 ^ (2 ^ (2 ^ gateHardSeedM0))

def gateRowThreshold (d : Nat) : Prop :=
  Nat.ceil ((2 : Real) ^ (Nat.log 2 (Params.r2 d) : Nat) *
    M2_hard_seed_rowDensity d * (Fintype.card (C1 d) : Real)) <=
      Fintype.card (C1 d)

def gateThreeFifths (d : Nat) : Prop :=
  forall c, c <= M2_T d + D (M1T d) ->
    (3 : Real) / 5 <=
      yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
        (Params.h2 d) c

def gateM2Robust (d : Nat) : Prop :=
  IsRobust (fun (c : C2 d) (r : R2 d) => M2 d r c)
    Params.delta (Params.b2 d)

theorem gate_hard_seed_threshold (d : Nat) (hpow : IsPow2 d)
    (hlog256 : 256 <= Nat.log 2 d)
    (hge : gateHardSeedThreshold <= d) :
    gateHardSeedM0 <= Nat.log 2 (Params.t2 d) := by
  rcases hpow with ⟨k, rfl⟩
  have hk256 : 256 <= k := by
    simpa [log_two_pow] using hlog256
  have hk_ne : k ≠ 0 := by omega
  have hkbig : 2 ^ (2 ^ gateHardSeedM0) <= k := by
    have hge' : 2 ^ (2 ^ (2 ^ gateHardSeedM0)) <= 2 ^ k := hge
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hge'
  have hlogk_big : 2 ^ gateHardSeedM0 <= Nat.log 2 k := by
    exact (Nat.le_log_iff_pow_le (by norm_num : 1 < 2) hk_ne).2 hkbig
  have ht2ge : 3 * Nat.log 2 (Nat.log 2 (2 ^ k)) + 2 <=
      Params.t2 (2 ^ k) :=
    Params.t2_ge (d := 2 ^ k) (by simpa [log_two_pow] using hk256)
  have hpow_le_t2 : 2 ^ gateHardSeedM0 <= Params.t2 (2 ^ k) := by
    rw [log_two_pow] at ht2ge
    omega
  exact
    (Nat.le_log_iff_pow_le (by norm_num : 1 < 2)
      (Nat.ne_of_gt (Params.t2_pos (2 ^ k)))).2 hpow_le_t2

theorem gate_row_density_scaled_le_one (d : Nat) (hpow : IsPow2 d)
    (hchk : Checklist d) :
    (2 : Real) ^ (Nat.log 2 (Params.r2 d) : Nat) *
      M2_hard_seed_rowDensity d <= 1 := by
  rcases hpow with ⟨k, rfl⟩
  have hr2pow : Params.r2 (2 ^ k) = 2 ^ Nat.log 2 (Params.r2 (2 ^ k)) :=
    ctor_r2_eq_two_pow_log (d := 2 ^ k) ⟨k, rfl⟩ hchk
  have hprod : Params.r2 (2 ^ k) * Params.t2 (2 ^ k) = 2 ^ k := by
    calc
      Params.r2 (2 ^ k) * Params.t2 (2 ^ k) = Params.q2 (2 ^ k) := hchk.q2_eq.symm
      _ = 2 ^ k := hchk.q2_eq_self
  have hb1 : Params.b1 (2 ^ k) = 2 * k := by
    unfold Params.b1
    rw [log_two_pow]
  have hr2real :
      (2 : Real) ^ (Nat.log 2 (Params.r2 (2 ^ k)) : Nat) =
        (Params.r2 (2 ^ k) : Real) := by
    exact_mod_cast hr2pow.symm
  have ht2real :
      (2 : Real) ^ (Nat.log 2 (Params.t2 (2 ^ k)) : Nat) =
        (Params.t2 (2 ^ k) : Real) := by
    rw [M2num_log2_t2_eq_M2_T]
    exact_mod_cast (M2num_t2_eq_two_pow_M2_T (2 ^ k)).symm
  calc
    (2 : Real) ^ (Nat.log 2 (Params.r2 (2 ^ k)) : Nat) *
        M2_hard_seed_rowDensity (2 ^ k)
        = (Params.r2 (2 ^ k) : Real) *
            ((Params.t2 (2 ^ k) : Real) *
              (2 : Real) ^ (-(Params.b1 (2 ^ k) : Real))) := by
          simp [M2_hard_seed_rowDensity, hr2real, ht2real]
    _ = ((Params.r2 (2 ^ k) * Params.t2 (2 ^ k) : Nat) : Real) *
          (2 : Real) ^ (-(Params.b1 (2 ^ k) : Real)) := by
          norm_num [Nat.cast_mul]
          ring
    _ = ((2 ^ k : Nat) : Real) * (2 : Real) ^ (-((2 * k : Nat) : Real)) := by
          rw [hprod, hb1]
    _ = (2 : Real) ^ (-(k : Real)) := by
          rw [show ((2 ^ k : Nat) : Real) = (2 : Real) ^ k by norm_num]
          rw [<- Real.rpow_natCast]
          have hcast : ((2 * k : Nat) : Real) = 2 * (k : Real) := by norm_num
          rw [hcast]
          rw [<- Real.rpow_add (by norm_num : (0 : Real) < 2)]
          congr 1
          ring
    _ <= 1 := by
          exact Real.rpow_le_one_of_one_le_of_nonpos
            (by norm_num : (1 : Real) <= 2)
            (neg_nonpos.mpr (Nat.cast_nonneg k))

theorem gate_row_threshold_proved (d : Nat) (hpow : IsPow2 d)
    (hchk : Checklist d) :
    gateRowThreshold d := by
  have hscale := gate_row_density_scaled_le_one d hpow hchk
  unfold gateRowThreshold
  apply Nat.ceil_le.mpr
  have hcard_nonneg : 0 <= (Fintype.card (C1 d) : Real) := by positivity
  calc
    (2 : Real) ^ (Nat.log 2 (Params.r2 d) : Nat) *
        M2_hard_seed_rowDensity d * (Fintype.card (C1 d) : Real)
        <= 1 * (Fintype.card (C1 d) : Real) := by
          exact mul_le_mul_of_nonneg_right hscale hcard_nonneg
    _ = (Fintype.card (C1 d) : Real) := by ring

theorem gate_M1T_complexity (d : Nat) (hpow : IsPow2 d)
    (hlog64 : 64 <= Nat.log 2 d) :
    D (M1T d) = Params.a d + 1 := by
  simpa [M1T] using (comp_transpose (M1 d)).trans (M1_complexity d hpow hlog64)

theorem gate_M2_T_le_loglog_add_four (d : Nat) (hpow : IsPow2 d)
    (hlog256 : 256 <= Nat.log 2 d) :
    M2_T d <= Nat.log 2 (Nat.log 2 d) + 4 := by
  rcases hpow with ⟨k, rfl⟩
  have hk256 : 256 <= k := by
    simpa [log_two_pow] using hlog256
  have hk_ne : k ≠ 0 := by omega
  set ell := Nat.log 2 k with hell
  have hell_pos : 1 <= ell := by
    rw [hell]
    exact (Nat.le_log_iff_pow_le (by norm_num : 1 < 2) hk_ne).2 (by omega)
  have ht2_le : Params.t2 (2 ^ k) <= 6 * k := by
    have hll : 1 <= Nat.log 2 (Nat.log 2 (2 ^ k)) := by
      simpa [log_two_pow, hell] using hell_pos
    simpa [log_two_pow] using Params.t2_le (d := 2 ^ k) hll
  have hk_lt : k < 2 ^ (ell + 1) := by
    simpa [hell, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (b := 2) (by norm_num : 1 < 2) k
  have h6k_lt : 6 * k < 2 ^ (ell + 4) := by
    calc
      6 * k < 6 * 2 ^ (ell + 1) := Nat.mul_lt_mul_of_pos_left hk_lt (by norm_num)
      _ <= 2 ^ (ell + 4) := by
        have hrewrite : 2 ^ (ell + 4) = 8 * 2 ^ (ell + 1) := by
          rw [show ell + 4 = 3 + (ell + 1) by omega, pow_add]
          norm_num
        rw [hrewrite]
        exact Nat.mul_le_mul_right (2 ^ (ell + 1)) (by norm_num : 6 <= 8)
  have hpowT_lt : 2 ^ M2_T (2 ^ k) < 2 ^ (ell + 4) := by
    rw [<- M2num_t2_eq_two_pow_M2_T (2 ^ k)]
    exact lt_of_le_of_lt ht2_le h6k_lt
  have hT_lt : M2_T (2 ^ k) < ell + 4 :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpowT_lt
  rw [log_two_pow]
  omega

theorem gate_a_le_two_loglog_add_three (d : Nat) (hpow : IsPow2 d)
    (hlog256 : 256 <= Nat.log 2 d) :
    Params.a d <= 2 * Nat.log 2 (Nat.log 2 d) + 3 := by
  rcases hpow with ⟨k, rfl⟩
  have hk256 : 256 <= k := by
    simpa [log_two_pow] using hlog256
  set ell := Nat.log 2 k with hell
  have hk_lt : k < 2 ^ (ell + 1) := by
    simpa [hell, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (b := 2) (by norm_num : 1 < 2) k
  unfold Params.a
  rw [log_two_pow]
  rw [<- hell]
  apply Nat.clog_le_of_le_pow
  exact le_of_lt (by
  calc
    2 * k ^ 2 < 2 * (2 ^ (ell + 1)) ^ 2 := by
      exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left hk_lt (by norm_num : (2 : Nat) ≠ 0))
        (by norm_num)
    _ = 2 ^ (2 * ell + 3) := by
      rw [show 2 * (2 ^ (ell + 1)) ^ 2 = 2 ^ 1 * (2 ^ (ell + 1)) ^ 2 by norm_num]
      rw [<- pow_mul, <- pow_add]
      congr 1
      omega)

theorem gate_h2prime_bridge_exp (d : Nat) (hpow : IsPow2 d)
    (hlog : 2 ^ 18 <= Nat.log 2 d) :
    M2_h2prime_bridge_exp d := by
  have hlog256 : 256 <= Nat.log 2 d := by omega
  have hlog64 : 64 <= Nat.log 2 d := by omega
  unfold M2_h2prime_bridge_exp Params.b2 Params.b2'
  rw [gate_M1T_complexity d hpow hlog64]
  have hT := gate_M2_T_le_loglog_add_four d hpow hlog256
  have ha := gate_a_le_two_loglog_add_three d hpow hlog256
  have hell18 : 18 <= Nat.log 2 (Nat.log 2 d) := by
    rcases hpow with ⟨k, rfl⟩
    have hk : 2 ^ 18 <= k := by
      simpa [log_two_pow] using hlog
    rw [log_two_pow]
    exact (Nat.le_log_iff_pow_le (by norm_num : 1 < 2)
      (by omega : k ≠ 0)).2 hk
  omega

structure GateDischargePartial (d : Nat) : Prop where
  hchk : Checklist d
  hlog : 2 ^ 18 <= Nat.log 2 d
  hm0_le :
    (Classical.choose
      (hard_seed.{0} Params.jSurplus (by norm_num [Params.jSurplus])
        Params.delta (by norm_num [Params.delta])
        (by norm_num [Params.delta])) : Nat) <= Nat.log 2 (Params.t2 d)
  hrow_threshold : gateRowThreshold d
  hprime : M2_h2prime_bridge_exp d

theorem large_d_checklist_partial :
    exists d0 : Nat, forall d : Nat, IsPow2 d -> d0 <= d ->
      GateDischargePartial d := by
  refine ⟨max large_d_checklist_strong.choose gateHardSeedThreshold, ?_⟩
  intro d hpow hge
  have hge_strong : large_d_checklist_strong.choose <= d := le_trans (Nat.le_max_left _ _) hge
  have hge_seed : gateHardSeedThreshold <= d := le_trans (Nat.le_max_right _ _) hge
  have hbase := large_d_checklist_strong.choose_spec d hpow hge_strong
  exact
    { hchk := hbase.1
      hlog := hbase.2
      hm0_le := by
        simpa [gateHardSeedM0] using
          gate_hard_seed_threshold d hpow (by omega) hge_seed
      hrow_threshold := gate_row_threshold_proved d hpow hbase.1
      hprime := gate_h2prime_bridge_exp d hpow hbase.2 }

-- CLAIM-END aux:gate-discharge-partial

-- CLAIM-BEGIN aux:gate-g3g5

private theorem gate_two_zpow_neg_nat_eq_rpow_neg_nat (n : Nat) :
    (2 : Real) ^ (-(n : Int)) = (2 : Real) ^ (-(n : Real)) := by
  have hcast : (((-(n : Int) : Int) : Real) = -(n : Real)) := by norm_num
  rw [hcast.symm]
  exact (Real.rpow_intCast (2 : Real) (-(n : Int))).symm

private lemma gate_eight_mul_le_two_pow {n : Nat} (hn : 6 <= n) :
    8 * n <= 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge n 6 with hnlt | hnge
      · have hn5 : n = 5 := by omega
        subst hn5
        norm_num
      · have hih := ih hnge
        have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
        omega

private lemma gate_log_le_div_eight {k : Nat} (hk : 64 <= k) :
    Nat.log 2 k <= k / 8 := by
  have hlog6 : 6 <= Nat.log 2 k := by
    calc
      6 = Nat.log 2 64 := by norm_num [Nat.log]
      _ <= Nat.log 2 k := Nat.log_mono_right hk
  have h8 : 8 * Nat.log 2 k <= 2 ^ Nat.log 2 k :=
    gate_eight_mul_le_two_pow hlog6
  have hpow : 2 ^ Nat.log 2 k <= k :=
    Nat.pow_log_le_self 2 (by omega)
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 8)]
  nlinarith

private lemma gate_self_le_two_pow_half {n : Nat} (hn : 64 <= n) :
    n <= 2 ^ (n / 2) := by
  have hlog8 : Nat.log 2 n <= n / 8 := gate_log_le_div_eight hn
  have hlog_half : Nat.log 2 n + 1 <= n / 2 := by omega
  have hlt : n < 2 ^ (Nat.log 2 n + 1) :=
    Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
  exact Nat.le_of_lt
    (lt_of_lt_of_le hlt
      (Nat.pow_le_pow_right (by norm_num : 1 <= 2) hlog_half))

private theorem gate_t2_ge_two_pow_loglog_div_two (d : Nat)
    (hpow : IsPow2 d)
    (hell64 : 64 <= Nat.log 2 (Nat.log 2 d)) :
    2 ^ (Nat.log 2 (Nat.log 2 d) / 2) <= Params.t2 d := by
  rcases hpow with ⟨k, rfl⟩
  set ell := Nat.log 2 k with hell
  have hell64' : 64 <= ell := by
    simpa [log_two_pow, hell] using hell64
  have hellpos : 0 < ell := by omega
  have hk_ne : k ≠ 0 := by
    intro hk
    rw [hk] at hell
    have : ell = 0 := by simp [hell]
    omega
  have hpow_le_k : 2 ^ ell <= k := Nat.pow_log_le_self 2 hk_ne
  have hell_self : ell <= 2 ^ (ell / 2) :=
    gate_self_le_two_pow_half hell64'
  have hmul_le_pow : ell * 2 ^ (ell / 2) <= 2 ^ ell := by
    calc
      ell * 2 ^ (ell / 2) <= 2 ^ (ell / 2) * 2 ^ (ell / 2) := by
        exact Nat.mul_le_mul_right (2 ^ (ell / 2)) hell_self
      _ = 2 ^ (ell / 2 + ell / 2) := by rw [← pow_add]
      _ <= 2 ^ ell := by
        exact Nat.pow_le_pow_right (by norm_num : 1 <= 2) (by omega)
  have hmul_le_k : ell * 2 ^ (ell / 2) <= k :=
    le_trans hmul_le_pow hpow_le_k
  have hdiv : 2 ^ (ell / 2) <= k / ell := by
    rw [Nat.le_div_iff_mul_le hellpos]
    simpa [Nat.mul_comm] using hmul_le_k
  have hdiv_le_inner :
      k / ell <= (3 * k + ell - 1) / ell := by
    exact Nat.div_le_div_right (by omega : k <= 3 * k + ell - 1)
  have hceil :
      (3 * Nat.log 2 (2 ^ k) + Nat.log 2 (Nat.log 2 (2 ^ k)) - 1) /
        Nat.log 2 (Nat.log 2 (2 ^ k)) <= Params.t2 (2 ^ k) := by
    unfold Params.t2
    exact le_ceilPowTwo _
  calc
    2 ^ (Nat.log 2 (Nat.log 2 (2 ^ k)) / 2)
        = 2 ^ (ell / 2) := by simp [hell]
    _ <= k / ell := hdiv
    _ <= (3 * k + ell - 1) / ell := hdiv_le_inner
    _ = (3 * Nat.log 2 (2 ^ k) + Nat.log 2 (Nat.log 2 (2 ^ k)) - 1) /
        Nat.log 2 (Nat.log 2 (2 ^ k)) := by simp [hell]
    _ <= Params.t2 (2 ^ k) := hceil

private theorem gate_M2_T_ge_loglog_div_two (d : Nat)
    (hpow : IsPow2 d)
    (hell64 : 64 <= Nat.log 2 (Nat.log 2 d)) :
    Nat.log 2 (Nat.log 2 d) / 2 <= M2_T d := by
  have ht2 := gate_t2_ge_two_pow_loglog_div_two d hpow hell64
  rw [M2num_t2_eq_two_pow_M2_T d] at ht2
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp ht2

private lemma gate_const_mul_sq_le_pow {m : Nat} (hm : 16 <= m) :
    200 * m ^ 2 <= 2 ^ m := by
  induction m with
  | zero => omega
  | succ m ih =>
      rcases Nat.lt_or_ge m 16 with hlt | hge
      · have hm15 : m = 15 := by omega
        subst hm15
        norm_num
      · have hih := ih hge
        have hquad : (m + 1) ^ 2 <= 2 * m ^ 2 := by nlinarith
        have hstep : 200 * (m + 1) ^ 2 <= 2 * (200 * m ^ 2) := by
          nlinarith
        have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
        omega

private lemma gate_log_sq_bound {n : Nat} (hn : 2 ^ 16 <= n) :
    2 * (10 * Nat.log 2 n) ^ 2 <= n := by
  let m := Nat.log 2 n
  have hn_ne : n ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos 16) hn)
  have hm16 : 16 <= m := by
    dsimp [m]
    exact (Nat.le_log_iff_pow_le (by norm_num : 1 < 2) hn_ne).2 hn
  have hconst : 200 * m ^ 2 <= 2 ^ m :=
    gate_const_mul_sq_le_pow hm16
  have hpow : 2 ^ m <= n := by
    dsimp [m]
    exact Nat.pow_log_le_self 2 hn_ne
  calc
    2 * (10 * Nat.log 2 n) ^ 2 = 200 * m ^ 2 := by
      dsimp [m]
      ring
    _ <= 2 ^ m := hconst
    _ <= n := hpow

noncomputable def gateG3G5LogThreshold : Nat :=
  2 ^ (2 ^ 16)

noncomputable def gateG3G5Threshold : Nat :=
  2 ^ gateG3G5LogThreshold

theorem gate_loglog_ge_g3g5_threshold (d : Nat) (hpow : IsPow2 d)
    (hge : gateG3G5Threshold <= d) :
    2 ^ 16 <= Nat.log 2 (Nat.log 2 d) := by
  rcases hpow with ⟨k, rfl⟩
  unfold gateG3G5Threshold at hge
  have hk0 : gateG3G5LogThreshold <= k :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hge
  have hk : 2 ^ (2 ^ 16) <= k := by
    change gateG3G5LogThreshold <= k
    exact hk0
  rw [log_two_pow]
  calc
    2 ^ 16 = Nat.log 2 (2 ^ (2 ^ 16)) := by rw [log_two_pow]
    _ <= Nat.log 2 k := Nat.log_mono_right hk

theorem gate_hard_seed_to_h2prime_exp (d : Nat) (hpow : IsPow2 d)
    (hll : 2 ^ 16 <= Nat.log 2 (Nat.log 2 d)) :
    M2_hard_seed_to_h2prime_exp d := by
  let ell := Nat.log 2 (Nat.log 2 d)
  let m := Nat.log 2 ell
  have hell64 : 64 <= ell := by
    dsimp [ell]
    exact le_trans (by norm_num : (64 : Nat) <= 2 ^ 16) hll
  have hTlower : ell / 2 <= M2_T d := by
    dsimp [ell]
    exact gate_M2_T_ge_loglog_div_two d hpow hell64
  have hsq2 : 2 * (10 * m) ^ 2 <= ell := by
    dsimp [m, ell]
    exact gate_log_sq_bound hll
  have hsq_half : (10 * m) ^ 2 <= ell / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    simpa [Nat.mul_comm] using hsq2
  have hsqT : (10 * m) ^ 2 <= M2_T d :=
    le_trans hsq_half hTlower
  have hsqrt : 10 * (m : Real) <= Real.sqrt (M2_T d : Real) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    exact_mod_cast hsqT
  have hexp :
      ((4 * m : Nat) : Real) <=
        (49 / 100 : Real) * Real.sqrt (M2_T d : Real) := by
    have hcast : ((4 * m : Nat) : Real) = 4 * (m : Real) := by norm_num
    rw [hcast]
    nlinarith [hsqrt]
  have hell_ne : ell ≠ 0 := by omega
  have hm16 : 16 <= m := by
    dsimp [m]
    exact (Nat.le_log_iff_pow_le (by norm_num : 1 < 2) hell_ne).2 hll
  have hell_lt : ell < 2 ^ (m + 1) := by
    dsimp [m]
    exact Nat.lt_pow_succ_log_self (b := 2) (by norm_num) ell
  have h8lt : 8 * ell < 2 ^ (m + 4) := by
    calc
      8 * ell < 8 * 2 ^ (m + 1) := by
        exact Nat.mul_lt_mul_of_pos_left hell_lt (by norm_num)
      _ = 2 ^ (m + 4) := by
        rw [show (8 : Nat) = 2 ^ 3 by norm_num, ← pow_add]
        congr 1
        omega
  have hnat : 8 * ell <= 2 ^ (4 * m) := by
    exact le_trans (Nat.le_of_lt h8lt)
      (Nat.pow_le_pow_right (by norm_num : 1 <= 2) (by omega))
  unfold M2_hard_seed_to_h2prime_exp Params.b2'
  change ((8 * ell : Nat) : Real) <=
    (2 : Real) ^ ((49 / 100 : Real) * Real.sqrt (M2_T d : Real))
  calc
    ((8 * ell : Nat) : Real) <= ((2 ^ (4 * m) : Nat) : Real) := by
      exact_mod_cast hnat
    _ = (2 : Real) ^ (4 * m : Nat) := by norm_num
    _ = (2 : Real) ^ (((4 * m : Nat) : Real)) := by
      rw [Real.rpow_natCast]
    _ <= (2 : Real) ^ ((49 / 100 : Real) * Real.sqrt (M2_T d : Real)) := by
      exact Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : Real) <= 2) hexp

private lemma gate_linear_le_two_pow_half {ell : Nat} (hell64 : 64 <= ell) :
    12 * ell + 18 <= 2 ^ (ell / 2) := by
  have hlog8 : Nat.log 2 ell <= ell / 8 := gate_log_le_div_eight hell64
  have hlog_half : Nat.log 2 ell + 5 <= ell / 2 := by omega
  have hell_lt : ell < 2 ^ (Nat.log 2 ell + 1) :=
    Nat.lt_pow_succ_log_self (b := 2) (by norm_num) ell
  have hlin_lt : 12 * ell + 18 < 2 ^ (Nat.log 2 ell + 5) := by
    have hell_pos : 0 < ell := by omega
    calc
      12 * ell + 18 <= 13 * ell := by nlinarith
      _ < 13 * 2 ^ (Nat.log 2 ell + 1) := by
        exact Nat.mul_lt_mul_of_pos_left hell_lt (by norm_num)
      _ <= 16 * 2 ^ (Nat.log 2 ell + 1) := by
        exact Nat.mul_le_mul_right _ (by norm_num : (13 : Nat) <= 16)
      _ = 2 ^ (Nat.log 2 ell + 5) := by
        rw [show (16 : Nat) = 2 ^ 4 by norm_num, ← pow_add]
        congr 1
        omega
  exact Nat.le_of_lt
    (lt_of_lt_of_le hlin_lt
      (Nat.pow_le_pow_right (by norm_num : 1 <= 2) hlog_half))

theorem gate_three_fifths_budget (d : Nat) (hpow : IsPow2 d)
    (hell64 : 64 <= Nat.log 2 (Nat.log 2 d)) :
    2 * (Params.b2 d + (M2_T d + D (M1T d)) + 1) <= Params.t2 d := by
  have ht2lower := gate_t2_ge_two_pow_loglog_div_two d hpow hell64
  have hlog256 : 256 <= Nat.log 2 d := by
    rcases hpow with ⟨k, rfl⟩
    set ell := Nat.log 2 k with hell
    have hell64' : 64 <= ell := by
      simpa [log_two_pow, hell] using hell64
    have hk_ne : k ≠ 0 := by
      intro hk
      rw [hk] at hell
      have : ell = 0 := by simp [hell]
      omega
    have hpow_le : 2 ^ ell <= k := Nat.pow_log_le_self 2 hk_ne
    rw [log_two_pow]
    have h256_le : (256 : Nat) <= 2 ^ ell := by
      calc
        (256 : Nat) = 2 ^ 8 := by norm_num
        _ <= 2 ^ ell := Nat.pow_le_pow_right (by norm_num : 1 <= 2) (by omega)
    exact le_trans h256_le hpow_le
  have hlog64 : 64 <= Nat.log 2 d := by omega
  have hT := gate_M2_T_le_loglog_add_four d hpow hlog256
  have ha := gate_a_le_two_loglog_add_three d hpow hlog256
  have hD := gate_M1T_complexity d hpow hlog64
  let ell := Nat.log 2 (Nat.log 2 d)
  have hA :
      Params.b2 d + (M2_T d + D (M1T d)) + 1 <= 6 * ell + 9 := by
    unfold Params.b2
    rw [hD]
    dsimp [ell]
    nlinarith [hT, ha]
  have hlin : 12 * ell + 18 <= 2 ^ (ell / 2) := by
    exact gate_linear_le_two_pow_half (by simpa [ell] using hell64)
  calc
    2 * (Params.b2 d + (M2_T d + D (M1T d)) + 1)
        <= 2 * (6 * ell + 9) := by
          exact Nat.mul_le_mul_left 2 hA
    _ = 12 * ell + 18 := by ring
    _ <= 2 ^ (ell / 2) := hlin
    _ = 2 ^ (Nat.log 2 (Nat.log 2 d) / 2) := by rfl
    _ <= Params.t2 d := ht2lower

private theorem gate_three_fifths_const :
    (3 : Real) / 5 <= (2 : Real) ^ (-(1 / 2 : Real)) := by
  rw [Real.rpow_neg (by norm_num : (0 : Real) <= 2)]
  rw [← Real.sqrt_eq_rpow]
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hmul : (3 : Real) / 5 * Real.sqrt 2 <= 1 := by
    have hnonneg : 0 <= (3 : Real) / 5 * Real.sqrt 2 := by positivity
    have hsquare :
        ((3 : Real) / 5 * Real.sqrt 2) ^ 2 <= (1 : Real) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : Real) <= 2)]
      norm_num
    have habs := (sq_le_sq).mp hsquare
    have habs_left : |(3 : Real) / 5 * Real.sqrt 2| =
        (3 : Real) / 5 * Real.sqrt 2 := abs_of_nonneg hnonneg
    simpa [habs_left] using habs
  rw [show (Real.sqrt 2)⁻¹ = (1 : Real) / Real.sqrt 2 by rw [one_div]]
  rw [le_div_iff₀ hsqrt_pos]
  simpa using hmul

theorem gate_yLoss_three_fifths_of_budget (d c : Nat)
    (hbudget : 2 * (Params.b2 d + c + 1) <= Params.t2 d) :
    (3 : Real) / 5 <=
      yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
        (Params.h2 d) c := by
  let A : Nat := Params.b2 d + c + 1
  let t : Nat := Params.t2 d
  let eps : Real := epsQT (Params.q2 d) (Params.t2 d)
  let base : Real := (Params.h2 d * (2 : Real) ^ (-(c : Real))) / (1 + eps)
  have htpos_nat : 0 < t := by dsimp [t]; exact Params.t2_pos d
  have heps_le : eps <= 1 := by
    dsimp [eps]
    exact le_trans (epsQT_le_half (Params.q2_pos d) (Params.t2_pos d))
      (by norm_num : (1 / 2 : Real) <= 1)
  have heps_pos : 0 < eps := by
    dsimp [eps]
    exact epsQT_pos (Params.q2_pos d) (Params.t2_pos d)
  have hdenpos : 0 < 1 + eps := by linarith
  have hnum_nonneg :
      0 <= Params.h2 d * (2 : Real) ^ (-(c : Real)) := by
    exact mul_nonneg (le_of_lt Params.h2_pos) (by positivity)
  have hbase_ge_half :
      Params.h2 d * (2 : Real) ^ (-(c : Real)) / 2 <= base := by
    dsimp [base]
    exact div_le_div_of_nonneg_left hnum_nonneg hdenpos (by linarith)
  have hhalf_eq :
      Params.h2 d * (2 : Real) ^ (-(c : Real)) / 2 =
        (2 : Real) ^ (-(A : Real)) := by
    have htwo_pos : (0 : Real) < 2 := by norm_num
    have hcastA : (A : Real) = (Params.b2 d : Real) + (c : Real) + 1 := by
      dsimp [A]
      norm_num
    unfold Params.h2
    rw [gate_two_zpow_neg_nat_eq_rpow_neg_nat (Params.b2 d)]
    calc
      (2 : Real) ^ (-(Params.b2 d : Real)) *
            (2 : Real) ^ (-(c : Real)) / 2
          = (2 : Real) ^ (-(Params.b2 d : Real)) *
              (2 : Real) ^ (-(c : Real)) * (2 : Real) ^ (-1 : Real) := by
                rw [Real.rpow_neg_one]
                ring_nf
      _ = (2 : Real) ^
            (-(Params.b2 d : Real) + -(c : Real) + (-1 : Real)) := by
              rw [← Real.rpow_add htwo_pos, ← Real.rpow_add htwo_pos]
      _ = (2 : Real) ^ (-(A : Real)) := by
              rw [hcastA]
              congr 1
              ring
  have hpowA_le_base : (2 : Real) ^ (-(A : Real)) <= base := by
    rw [← hhalf_eq]
    exact hbase_ge_half
  have htpos_real : 0 < (t : Real) := by exact_mod_cast htpos_nat
  have hA_half : (A : Real) * (1 / (t : Real)) <= 1 / 2 := by
    have hbudget_real : (2 : Real) * (A : Real) <= (t : Real) := by
      dsimp [A, t] at hbudget ⊢
      exact_mod_cast hbudget
    rw [mul_one_div]
    rw [div_le_iff₀ htpos_real]
    nlinarith
  have hexp : (-(1 / 2 : Real)) <= -(A : Real) * (1 / (t : Real)) := by
    nlinarith
  have hroot_const :
      (2 : Real) ^ (-(1 / 2 : Real)) <=
        ((2 : Real) ^ (-(A : Real))) ^ (1 / (t : Real)) := by
    rw [← Real.rpow_mul (by norm_num : (0 : Real) <= 2)]
    exact Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : Real) <= 2) hexp
  have hbase0 : 0 <= (2 : Real) ^ (-(A : Real)) := by positivity
  have hroot_le :
      ((2 : Real) ^ (-(A : Real))) ^ (1 / (t : Real)) <=
        base ^ (1 / (t : Real)) := by
    exact Real.rpow_le_rpow hbase0 hpowA_le_base (by positivity)
  unfold yLoss
  dsimp [base, eps, t] at hroot_le
  exact le_trans gate_three_fifths_const (le_trans hroot_const hroot_le)

theorem gate_three_fifths (d : Nat) (hpow : IsPow2 d)
    (hll : 2 ^ 16 <= Nat.log 2 (Nat.log 2 d)) :
    gateThreeFifths d := by
  intro c hc
  have hell64 : 64 <= Nat.log 2 (Nat.log 2 d) :=
    le_trans (by norm_num : (64 : Nat) <= 2 ^ 16) hll
  have hmain := gate_three_fifths_budget d hpow hell64
  apply gate_yLoss_three_fifths_of_budget
  have hA :
      Params.b2 d + c + 1 <=
        Params.b2 d + (M2_T d + D (M1T d)) + 1 := by
    omega
  exact le_trans (Nat.mul_le_mul_left 2 hA) hmain

theorem large_d_checklist_g3g5 :
    exists d0 : Nat, forall d : Nat, IsPow2 d -> d0 <= d ->
      GateDischargePartial d /\ M2_hard_seed_to_h2prime_exp d /\
        gateThreeFifths d := by
  refine ⟨max large_d_checklist_partial.choose gateG3G5Threshold, ?_⟩
  intro d hpow hge
  have hge_partial : large_d_checklist_partial.choose <= d :=
    le_trans (Nat.le_max_left _ _) hge
  have hge_g3g5 : gateG3G5Threshold <= d :=
    le_trans (Nat.le_max_right _ _) hge
  have hpartial := large_d_checklist_partial.choose_spec d hpow hge_partial
  have hll := gate_loglog_ge_g3g5_threshold d hpow hge_g3g5
  exact ⟨hpartial, gate_hard_seed_to_h2prime_exp d hpow hll,
    gate_three_fifths d hpow hll⟩

-- CLAIM-END aux:gate-g3g5

-- CLAIM-BEGIN aux:gate-full

theorem CtorFullGates (d : Nat) (hpow : IsPow2 d)
    (hlog : 2 ^ 18 <= Nat.log 2 d) (hchk : Checklist d)
    (hm0_le :
      (Classical.choose
        (hard_seed.{0} Params.jSurplus (by norm_num [Params.jSurplus])
          Params.delta (by norm_num [Params.delta])
          (by norm_num [Params.delta])) : Nat) <= Nat.log 2 (Params.t2 d))
    (hrow_threshold : gateRowThreshold d)
    (hraw : M2_hard_seed_to_h2prime_exp d)
    (hprime : M2_h2prime_bridge_exp d)
    (hy_three_fifths : gateThreeFifths d) :
    gateM2Robust d := by
  have hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d) :=
    ctor_r2_eq_two_pow_log hpow hchk
  unfold gateM2Robust
  exact M2_robust_closed d hpow hlog hchk hm0_le hr2pow
    hrow_threshold hraw hprime hy_three_fifths

theorem large_d_checklist_full :
    exists d0 : Nat, forall d : Nat, IsPow2 d -> d0 <= d ->
      (GateDischargePartial d /\ M2_hard_seed_to_h2prime_exp d /\
        gateThreeFifths d) /\ gateM2Robust d := by
  refine ⟨large_d_checklist_g3g5.choose, ?_⟩
  intro d hpow hge
  have hgates := large_d_checklist_g3g5.choose_spec d hpow hge
  rcases hgates with ⟨hpartial, hraw, hy_three_fifths⟩
  have hrob : gateM2Robust d :=
    CtorFullGates d hpow hpartial.hlog hpartial.hchk hpartial.hm0_le
      hpartial.hrow_threshold hraw hpartial.hprime hy_three_fifths
  exact ⟨⟨hpartial, hraw, hy_three_fifths⟩, hrob⟩

-- CLAIM-END aux:gate-full

end NPCC
