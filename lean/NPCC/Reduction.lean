import Mathlib
import NPCC.Stage3
import NPCC.Size
import NPCC.GateDischarge

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace NPCC

open Workspace.Types.CommComplexity

-- CLAIM-BEGIN aux:ctor-gates

noncomputable def ctorDStar : Nat :=
  large_d_checklist_strong.choose

noncomputable def reducedInstance (I : VBPInstance) : PreprocessedInstance :=
  normalizeInstance ctorDStar (preprocess I)

noncomputable def ctorScale (I : VBPInstance) : Nat :=
  (reducedInstance I).d

noncomputable def reducedVectors (I : VBPInstance) :
    Fin (reducedInstance I).n -> Fin (Params.q2 (ctorScale I)) -> Bool :=
  fun i alpha =>
    (reducedInstance I).v i
      (Fin.cast
        (by
          have hpow :
              ctorScale I =
                2 ^ (normalizeInstance_d_two_pow ctorDStar (preprocess I)).choose := by
            exact (normalizeInstance_d_two_pow ctorDStar (preprocess I)).choose_spec
          exact Params.q2_eq_self hpow)
        alpha)

theorem ctorScale_eq_ceilPowTwo (I : VBPInstance) :
    ctorScale I = ceilPowTwo (max (preprocess I).d ctorDStar) := by
  rfl

theorem ctorScale_le_two_mul_max (I : VBPInstance)
    (hmax : 1 <= max (preprocess I).d ctorDStar) :
    ctorScale I <= 2 * max (preprocess I).d ctorDStar := by
  simpa [ctorScale_eq_ceilPowTwo I] using ceilPowTwo_le_two_mul hmax

theorem two_le_of_pow_log {d : Nat} (hpow : IsPow2 d)
    (hlog : 2 ^ 18 <= Nat.log 2 d) : 2 <= d := by
  cases hpow with
  | intro k hkpow =>
      rw [hkpow] at hlog
      rw [hkpow]
      have hk : 2 ^ 18 <= k := by
        simpa [log_two_pow] using hlog
      have hkpos : 0 < k := by omega
      exact Nat.succ_le_of_lt (Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp hkpos))

structure CtorScaleCertificate (I : VBPInstance) : Prop where
  hpow : IsPow2 (ctorScale I)
  hlog : 2 ^ 18 <= Nat.log 2 (ctorScale I)
  hchk : Checklist (ctorScale I)
  hd : 2 <= ctorScale I

theorem ctorScaleCertificate (I : VBPInstance) :
    CtorScaleCertificate I := by
  have hpow : IsPow2 (ctorScale I) := by
    simpa [ctorScale, reducedInstance] using
      normalizeInstance_d_two_pow ctorDStar (preprocess I)
  have hge : large_d_checklist_strong.choose <= ctorScale I := by
    simpa [ctorScale, reducedInstance, ctorDStar] using
      dstar_le_normalizeInstance_d ctorDStar (preprocess I)
  have hspec := large_d_checklist_strong.choose_spec (ctorScale I) hpow hge
  exact
    { hpow := hpow
      hlog := hspec.2
      hchk := hspec.1
      hd := two_le_of_pow_log hpow hspec.2 }

theorem ctor_a_add_two_le_t1 {d : Nat} (hpow : IsPow2 d)
    (hlog : 2 ^ 18 <= Nat.log 2 d) :
    Params.a d + 2 <= Params.t1 d := by
  cases hpow with
  | intro k hkpow =>
      rw [hkpow] at hlog
      rw [hkpow]
      have hkbig : 2 ^ 18 <= k := by
        simpa [log_two_pow] using hlog
      have hk1 : 1 <= k := by omega
      have hlog1 : 1 <= Nat.log 2 (2 ^ k) := by
        simpa [log_two_pow] using hk1
      have htlo : 64 * k <= Params.t1 (2 ^ k) := by
        have ht := (Params.t1_bracket (d := 2 ^ k) hlog1).1
        simpa [log_two_pow] using ht
      have ha_le : Params.a (2 ^ k) <= 2 * k := by
        unfold Params.a
        apply Nat.clog_le_of_le_pow
        rw [log_two_pow]
        have hsq := Nat.two_mul_sq_add_one_le_two_pow_two_mul k
        omega
      calc
        Params.a (2 ^ k) + 2 <= 2 * k + 2 := by omega
        _ <= 64 * k := by nlinarith
        _ <= Params.t1 (2 ^ k) := htlo

theorem ctor_eta2_lt_one {d : Nat} (hchk : Checklist d) :
    Params.eta2 d < 1 := by
  have heps_pos :
      0 < epsQT (2 ^ Params.a d + 3) (Params.t1 d) :=
    epsQT_pos (by positivity) (Params.t1_pos d)
  have hlt :
      (1 - epsQT (2 ^ Params.a d + 3) (Params.t1 d)) / 2 < (1 : Real) := by
    linarith
  exact lt_trans hchk.dens_eta_lt hlt

theorem ctor_r2_eq_two_pow_log {d : Nat} (hpow : IsPow2 d) (hchk : Checklist d) :
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

structure CtorGates (d : Nat) : Prop where
  hpow : IsPow2 d
  hlog : 2 ^ 18 <= Nat.log 2 d
  hchk : Checklist d
  hd : 2 <= d
  hlog256 : 256 <= Nat.log 2 d
  hlog64 : 64 <= Nat.log 2 d
  ht1_pos : 1 <= Params.t1 d
  ht2_pos : 1 <= Params.t2 d
  ht1_le_q1_add_five : Params.t1 d <= Params.q1 d + 5
  ht2_le_q2 : Params.t2 d <= Params.q2 d
  one_le_q1 : 1 <= Params.q1 d
  q2_eq : Params.q2 d = Params.r2 d * Params.t2 d
  q2_eq_self : Params.q2 d = d
  clog_q2_eq : Nat.clog 2 (Params.q2 d) = Nat.log 2 (Params.q2 d)
  m1_threshold : Params.a d + 2 <= Params.t1 d
  eta2_nonneg : 0 <= Params.eta2 d
  eta2_lt_one : Params.eta2 d < 1
  eta2_dense_gate :
    Params.eta2 d < (1 - epsQT (2 ^ Params.a d + 3) (Params.t1 d)) / 2
  r2_eq_two_pow_log : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d)
  m2_T_ge_five : 5 <= M2_T d
  m2_copy_lower : 2 ^ M2_T d <= 2 * M2_hard_seed_copies d
  m2_copy_upper : M2_hard_seed_copies d <= 2 ^ M2_T d
  m2_dense_qcast : 2 ^ M2DenseDepth d = Params.q2 d
  m2_rowDensity_le_one : M2_hard_seed_rowDensity d <= 1
  m1_terminal_density_le_one : M1_stage2_terminal_density d <= 1
  m1_terminal_row_estimate :
    9 * Params.t1 d <=
      16 * Nat.ceil ((Fintype.card (R1 d) : Real) *
        M1_stage2_terminal_density d)
  m1_terminal_col_estimate :
    (2 : Real) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : Int))
        * (Fintype.card (C1 d) : Real) <=
      (Nat.ceil ((Fintype.card (C1 d) : Real) *
        ((2 : Real) ^ (-(Params.b1 d : Int)))) : Real)
  m2_bridge_of_h2prime :
    M2_hard_seed_to_h2prime_exp d -> M2_h2prime_bridge_exp d ->
      M2_hard_seed_columnDensity d <=
        Params.h2 d *
          (2 : Real) ^ (-((M2_T d + D (M1T d) : Nat) : Real)) /
            (1 + epsQT (Params.q2 d) (Params.t2 d))
  m2_residual_density_of_three_fifths :
    (forall c, c <= M2_T d + D (M1T d) ->
      (3 : Real) / 5 <=
        yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
          (Params.h2 d) c) ->
    forall c, c <= M2_T d + D (M1T d) ->
      1 / 2 + Params.delta <=
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c /\
        yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c <= 1
  output_size :
    forall n : Nat,
      (Fintype.card (R4 d n) : Real) <= (n : Real) + rowPoly d /\
        (Fintype.card (C4 d) : Real) <= colPoly d

theorem ctorGates {d : Nat} (hpow : IsPow2 d)
    (hlog : 2 ^ 18 <= Nat.log 2 d) (hchk : Checklist d) :
    CtorGates d := by
  have hlog256 : 256 <= Nat.log 2 d := by omega
  have hT5 : 5 <= M2_T d := M2num_M2_T_ge_five d hlog256
  have hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d) :=
    ctor_r2_eq_two_pow_log hpow hchk
  exact
    { hpow := hpow
      hlog := hlog
      hchk := hchk
      hd := two_le_of_pow_log hpow hlog
      hlog256 := hlog256
      hlog64 := by omega
      ht1_pos := Params.t1_pos d
      ht2_pos := Params.t2_pos d
      ht1_le_q1_add_five := hchk.t1_le_q1_add_five
      ht2_le_q2 := hchk.t2_le_q2
      one_le_q1 := hchk.one_le_q1
      q2_eq := hchk.q2_eq
      q2_eq_self := hchk.q2_eq_self
      clog_q2_eq := hchk.clog_q2_eq
      m1_threshold := ctor_a_add_two_le_t1 hpow hlog
      eta2_nonneg := le_of_lt (Params.eta2_pos (d := d))
      eta2_lt_one := ctor_eta2_lt_one hchk
      eta2_dense_gate := hchk.dens_eta_lt
      r2_eq_two_pow_log := hr2pow
      m2_T_ge_five := hT5
      m2_copy_lower := M2num_hard_seed_copy_lower d hT5
      m2_copy_upper := M2num_hard_seed_copy_upper d hT5
      m2_dense_qcast := by
        calc
          2 ^ M2DenseDepth d =
              2 ^ (Nat.log 2 (Params.r2 d) + M2_T d) := rfl
          _ = 2 ^ Nat.log 2 (Params.r2 d) * 2 ^ M2_T d := by
              rw [pow_add]
          _ = Params.r2 d * Params.t2 d := by
              rw [<- hr2pow, <- M2num_t2_eq_two_pow_M2_T d]
          _ = Params.q2 d := hchk.q2_eq.symm
      m2_rowDensity_le_one := M2num_hard_seed_rowDensity_le_one d hchk
      m1_terminal_density_le_one := M1_terminal_density_le_one d
      m1_terminal_row_estimate := M1_terminal_row_estimate d hpow hlog
      m1_terminal_col_estimate := M1_terminal_col_estimate d
      m2_bridge_of_h2prime := by
        intro hraw hprime
        exact M2num_hbridge_via_h2prime d hraw hprime
      m2_residual_density_of_three_fifths := by
        intro hy
        exact M2num_residual_density_of_three_fifths d hy
      output_size := by
        intro n
        exact output_size_bounds d n (Params.t1_pos d) hchk.t1_le_q1_add_five
          (Params.t2_pos d) hchk.t2_le_q2 hchk.one_le_q1 }

-- CLAIM-END aux:ctor-gates

-- CLAIM-BEGIN aux:ctor-full

noncomputable def ctorDStarFull : Nat :=
  large_d_checklist_full.choose

noncomputable def reducedInstanceFull (I : VBPInstance) : PreprocessedInstance :=
  normalizeInstance ctorDStarFull (preprocess I)

noncomputable def ctorScaleFull (I : VBPInstance) : Nat :=
  (reducedInstanceFull I).d

theorem ctorScaleFull_eq_ceilPowTwo (I : VBPInstance) :
    ctorScaleFull I = ceilPowTwo (max (preprocess I).d ctorDStarFull) := by
  rfl

theorem CtorScaleCertificateFull (I : VBPInstance) :
    IsPow2 (ctorScaleFull I) /\
      2 ^ 18 <= Nat.log 2 (ctorScaleFull I) /\
      Checklist (ctorScaleFull I) /\
      2 <= ctorScaleFull I /\
      (Classical.choose
        (hard_seed.{0} Params.jSurplus (by norm_num [Params.jSurplus])
          Params.delta (by norm_num [Params.delta])
          (by norm_num [Params.delta])) : Nat) <=
        Nat.log 2 (Params.t2 (ctorScaleFull I)) /\
      gateRowThreshold (ctorScaleFull I) /\
      M2_hard_seed_to_h2prime_exp (ctorScaleFull I) /\
      M2_h2prime_bridge_exp (ctorScaleFull I) /\
      gateThreeFifths (ctorScaleFull I) /\
      IsRobust
        (fun (c : C2 (ctorScaleFull I)) (r : R2 (ctorScaleFull I)) =>
          M2 (ctorScaleFull I) r c)
        Params.delta (Params.b2 (ctorScaleFull I)) := by
  have hpow : IsPow2 (ctorScaleFull I) := by
    simpa [ctorScaleFull, reducedInstanceFull] using
      normalizeInstance_d_two_pow ctorDStarFull (preprocess I)
  have hge : large_d_checklist_full.choose <= ctorScaleFull I := by
    simpa [ctorScaleFull, reducedInstanceFull, ctorDStarFull] using
      dstar_le_normalizeInstance_d ctorDStarFull (preprocess I)
  have hspec := large_d_checklist_full.choose_spec (ctorScaleFull I) hpow hge
  rcases hspec with ⟨hgates, hrob⟩
  rcases hgates with ⟨hpartial, hraw, hy_three_fifths⟩
  exact
    ⟨hpow, hpartial.hlog, hpartial.hchk,
      two_le_of_pow_log hpow hpartial.hlog, hpartial.hm0_le,
      hpartial.hrow_threshold, hraw, hpartial.hprime, hy_three_fifths,
      by simpa [gateM2Robust] using hrob⟩

-- CLAIM-END aux:ctor-full

end NPCC
