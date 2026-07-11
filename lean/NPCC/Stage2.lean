import NPCC.Stage1
import NPCC.ComplexityAux
import Workspace.BracketLemmas

/-! # Stage-2 hardness and separation

This module applies the extension and separation machinery to the transpose of
`M₁`, producing the hard seed, exact Stage-2 complexity, robustness, and
protocol-control interfaces used by Stage 3. Numerical side conditions remain
explicit hypotheses until `Checklist` discharges them at final use sites.
-/

namespace NPCC

open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open Workspace.Types.BoolMat
open Workspace.Types.MatComplexity
open Workspace.Types.Protocol

/-- The Stage-2 base game, namely the transpose of `M1 d`. -/
noncomputable def M1T (d : ℕ) : C1 d → R1 d → Bool :=
  fun j a => M1 d a j

/-- The structural exponent whose power of two is exactly `t2 d`. -/
def M2_T (d : ℕ) : ℕ :=
  Nat.clog 2
    ((3 * Nat.log 2 d + Nat.log 2 (Nat.log 2 d) - 1) /
      Nat.log 2 (Nat.log 2 d))

/-- The copy count supplied by `lem:hard-seed` at the Stage-2 value `j = 5`. -/
def M2_hard_seed_copies (d : ℕ) : ℕ :=
  (2 ^ (Params.jSurplus - 1) + 2) *
    2 ^ (Nat.log 2 (Params.t2 d) - Params.jSurplus)

/-- The row density supplied by `lem:hard-seed` at `m = log t2`. -/
noncomputable def M2_hard_seed_rowDensity (d : ℕ) : ℝ :=
  (2 : ℝ) ^ (Nat.log 2 (Params.t2 d) : ℕ) *
    (2 : ℝ) ^ (-(Params.b1 d : ℝ))

/-- The terminal hard-seed column density before the comparison to `h2'`. -/
noncomputable def M2_hard_seed_columnDensity (d : ℕ) : ℝ :=
  (2 : ℝ) ^
    (-((2 : ℝ) ^
      ((49 / 100 : ℝ) * Real.sqrt (Nat.log 2 (Params.t2 d) : ℕ))))

private lemma two_zpow_neg_nat_eq_rpow_neg_nat_stage2 (n : ℕ) :
    (2 : ℝ) ^ (-(n : ℤ)) = (2 : ℝ) ^ (-(n : ℝ)) := by
  have hcast : (((-(n : ℤ) : ℤ) : ℝ) = -(n : ℝ)) := by norm_num
  rw [hcast.symm]
  exact (Real.rpow_intCast (2 : ℝ) (-(n : ℤ))).symm

/-- Typed one-copy transpose transport for bracket-family complexity. -/
private theorem Dfamily_one_transpose {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) :
    Dfamily (interlaceFun (fun yy xx => f xx yy) 1)
        (bracketGE Y X 1 y x)
      =
    Dfamily (interlaceFun f 1) (bracketGE X Y 1 x y) := by
  classical
  let eX : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm
  let eY : Fin (Fintype.card Y) ≃ Y := (Fintype.equivFin Y).symm
  let M : BoolMat :=
    ⟨Fintype.card X, Fintype.card Y, fun i j => f (eX i) (eY j)⟩
  have he : ∀ i j, M.e i j = f (eX i) (eY j) := fun _ _ => rfl
  have heT : ∀ i j, M.transpose.e i j =
      (fun yy xx => f xx yy) (eY i) (eX j) := fun _ _ => rfl
  have hleft :
      Dfamily (interlaceFun (fun yy xx => f xx yy) 1)
          (bracketGE Y X 1 y x)
        = DSet (Workspace.Types.Bracket.bracket M.transpose 1 y x) :=
    Dfamily_eq_DSet (fun yy xx => f xx yy) M.transpose eY eX heT
      hy0 hy1 hx0 hx1 hY
  have hright :
      Dfamily (interlaceFun f 1) (bracketGE X Y 1 x y)
        = DSet (Workspace.Types.Bracket.bracket M 1 x y) :=
    Dfamily_eq_DSet f M eX eY he hx0 hx1 hy0 hy1 hX
  rw [hleft, hright, Workspace.BracketLemmas.transpose_bracket]
  rfl

private theorem t2_eq_two_pow_log (d : ℕ) :
    Params.t2 d = 2 ^ Nat.log 2 (Params.t2 d) := by
  have ht2_clog :
      Params.t2 d =
        2 ^ Nat.clog 2
          ((3 * Nat.log 2 d + Nat.log 2 (Nat.log 2 d) - 1) /
            Nat.log 2 (Nat.log 2 d)) := rfl
  rw [ht2_clog, log_two_pow]

private theorem t2_eq_two_pow_M2_T (d : ℕ) :
    Params.t2 d = 2 ^ M2_T d := rfl

private theorem M1T_complexity (d : ℕ) (hpow : IsPow2 d)
    (hlog : 64 ≤ Nat.log 2 d) :
    D (M1T d) = Params.a d + 1 := by
  have htr : D (M1T d) = D (M1 d) := by
    simpa [M1T] using comp_transpose (M1 d)
  exact htr.trans (M1_complexity d hpow hlog)

private theorem one_le_M1_terminal_transpose (d : ℕ) (hpow : IsPow2 d)
    (hlog : 64 ≤ Nat.log 2 d)
    (hy_le_one : M1_stage2_terminal_density d ≤ 1)
    (hrowTerm : 9 * Params.t1 d ≤
      16 * ⌈(Fintype.card (R1 d) : ℝ) * M1_stage2_terminal_density d⌉₊)
    (hcolTerm : (2 : ℝ) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : ℤ))
        * (Fintype.card (C1 d) : ℝ) ≤
      (⌈(Fintype.card (C1 d) : ℝ) *
        ((2 : ℝ) ^ (-(Params.b1 d : ℤ)))⌉₊ : ℝ)) :
    1 ≤ Dfamily (interlaceFun (M1T d) 1)
      (bracketGE (C1 d) (R1 d) 1 ((2 : ℝ) ^ (-(Params.b1 d : ℝ)))
        (M1_stage2_terminal_density d)) := by
  classical
  have hd : 2 ≤ d := by
    obtain ⟨k, rfl⟩ := hpow
    have hk : 64 ≤ k := by simpa [log_two_pow] using hlog
    exact Nat.succ_le_of_lt (Nat.one_lt_two_pow (by omega : k ≠ 0))
  obtain ⟨hdiv, _hTb, _hRb, _hgap⟩ := M1_low_column_stage2_gates hpow hlog
  have hterm := M1_terminal_stage2 d hpow hlog hy_le_one hrowTerm hcolTerm
  have hcomplex := M1_complexity d hpow hlog
  have hcap := M1_capacity_log_identity d hd hdiv
  have hleft_ge : (1 : ℤ) ≤
      (D (M1 d) : ℤ) - (Nat.log 2 (Params.r1 d) : ℤ) := by
    rw [hcomplex, hcap]
    omega
  have hterm_one_int :
      (1 : ℤ) ≤
        (Dfamily (interlaceFun (M1 d) 1)
          (bracketGE (R1 d) (C1 d) 1 (M1_stage2_terminal_density d)
            ((2 : ℝ) ^ (-(Params.b1 d : ℤ)))) : ℤ) :=
    le_trans hleft_ge hterm
  have hterm_one :
      1 ≤
        Dfamily (interlaceFun (M1 d) 1)
          (bracketGE (R1 d) (C1 d) 1 (M1_stage2_terminal_density d)
            ((2 : ℝ) ^ (-(Params.b1 d : ℤ)))) := by
    exact_mod_cast hterm_one_int
  have hy_pos : 0 < M1_stage2_terminal_density d := by
    unfold M1_stage2_terminal_density yLoss
    apply Real.rpow_pos_of_pos
    apply div_pos
    · exact mul_pos Params.h2_pos (by positivity)
    · have hεpos : 0 < epsQT (Params.q2 d) (Params.t2 d) :=
        epsQT_pos (Params.q2_pos d) (Params.t2_pos d)
      linarith
  have hb_pos : 0 < (2 : ℝ) ^ (-(Params.b1 d : ℝ)) := by positivity
  have hb_le_one : (2 : ℝ) ^ (-(Params.b1 d : ℝ)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
    exact neg_nonpos.mpr (by positivity)
  have hRcard : 1 ≤ Fintype.card (R1 d) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    simpa using Params.one_le_q1 (by omega : 2 ≤ Nat.log 2 d)
  have hCcard : 1 ≤ Fintype.card (C1 d) := by
    have hchk : Params.t1 d ≤ Params.q1 d + 5 :=
      Params.t1_le_q1_add_five hlog
    simpa [C1, Fintype.card_fin] using L1_pos d hchk
  have htranspose :=
    Dfamily_one_transpose (M1 d)
      (x := M1_stage2_terminal_density d)
      (y := (2 : ℝ) ^ (-(Params.b1 d : ℝ)))
      hy_pos hy_le_one hb_pos hb_le_one hRcard hCcard
  have hterm_one_rpow :
      1 ≤
        Dfamily (interlaceFun (M1 d) 1)
          (bracketGE (R1 d) (C1 d) 1 (M1_stage2_terminal_density d)
            ((2 : ℝ) ^ (-(Params.b1 d : ℝ)))) := by
    rwa [two_zpow_neg_nat_eq_rpow_neg_nat_stage2 (Params.b1 d)] at hterm_one
  have hterm_trans :
      1 ≤ Dfamily (interlaceFun (fun yy xx => M1 d xx yy) 1)
        (bracketGE (C1 d) (R1 d) 1 ((2 : ℝ) ^ (-(Params.b1 d : ℝ)))
          (M1_stage2_terminal_density d)) := by
    rwa [htranspose]
  simpa [M1T] using hterm_trans

-- CLAIM-BEGIN lem:M2-column-loss-resilient
/-- Paper `lem:M2-column-loss-resilient`: the Stage-2 base matrix
`transpose M1` is column-loss resilient at `(q2, t2, h2)`.  The terminal
one-copy clause is proved from `M1_terminal_stage2`; the residual three-rung
Lambda estimates over all allowed column losses are exposed as an explicit
Stage-2 numeric/selection gate. -/
theorem M2_column_loss_resilient (d : ℕ) (hpow : IsPow2 d)
    (hlog : 64 ≤ Nat.log 2 d)
    (hy_le_one : M1_stage2_terminal_density d ≤ 1)
    (hrowTerm : 9 * Params.t1 d ≤
      16 * ⌈(Fintype.card (R1 d) : ℝ) * M1_stage2_terminal_density d⌉₊)
    (hcolTerm : (2 : ℝ) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : ℤ))
        * (Fintype.card (C1 d) : ℝ) ≤
      (⌈(Fintype.card (C1 d) : ℝ) *
        ((2 : ℝ) ^ (-(Params.b1 d : ℤ)))⌉₊ : ℝ))
    (hresidual : ∀ k ≤ D (M1T d),
      ∀ c ≤ M2_T d + k,
        D (M1T d) - k ≤
          LambdaGE (M1T d) 1 ((2 : ℝ) ^ (-(Params.b1 d : ℝ)))
            (yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
              (Params.h2 d) c)) :
    IsColumnLossResilient (M1T d) (Params.b1 d : ℝ)
      (epsQT (Params.q2 d) (Params.t2 d))
      (Nat.log 2 (Params.q2 d)) (M2_T d) (Params.h2 d) := by
-- CLAIM-END lem:M2-column-loss-resilient
  have hDswap : D (M1T d) = D (M1 d) := by
    simpa [M1T] using comp_transpose (M1 d)
  constructor
  · have hone :=
      one_le_M1_terminal_transpose d hpow hlog hy_le_one hrowTerm hcolTerm
    unfold M1_stage2_terminal_density at hone
    rw [← hDswap] at hone
    exact hone
  · intro k hk c hc
    exact hresidual k hk c hc

-- CLAIM-BEGIN aux:m2-midlayer
/-- Stage-2 `q₂` is a power of two by construction, with the exact `clog`
exponent.  This is the local Stage-2 copy of the bridge used by the direct
row-index protocol. -/
private theorem q2_eq_two_pow_clog_stage2 (d : ℕ) :
    Params.q2 d = 2 ^ Nat.clog 2 (Params.q2 d) := by
  have h : Nat.clog 2 (Params.q2 d) = Nat.clog 2 d := by
    rw [show Params.q2 d = 2 ^ Nat.clog 2 d from rfl,
      Nat.clog_pow 2 _ one_lt_two]
  rw [h]
  rfl

/-- Direct Stage-2 upper bound: Alice announces the outer Stage-2 row index
and the remaining branch maps each Stage-2 column to the corresponding
`M1T` column. -/
theorem M2_upper_bound (d : ℕ)
    (hclog : Nat.clog 2 (Params.q2 d) = Nat.log 2 (Params.q2 d)) :
    D (M2 d) ≤ D (M1 d) + Nat.log 2 (Params.q2 d) := by
  classical
  let Qlog := Nat.clog 2 (Params.q2 d)
  have hqpow : Params.q2 d = 2 ^ Qlog := q2_eq_two_pow_clog_stage2 d
  let σ : R2 d → Fin (2 ^ Qlog) := fun r => Fin.cast hqpow r.1
  have hpart : D (M2 d) ≤ Qlog + D (M1 d) := by
    refine comp_le_partition (M2 d) Qlog (D (M1 d)) σ ?_
    intro k
    let α : Fin (Params.q2 d) := Fin.cast hqpow.symm k
    have hmap :
        D (fun (x : {x : R2 d // σ x = k}) (c : C2 d) =>
          M1T d x.val.2 (S2fam d c α)) ≤ D (M1T d) :=
      D_mapNodes_le (M1T d)
        (fun x : {x : R2 d // σ x = k} => x.val.2)
        (fun c : C2 d => S2fam d c α)
    have hbranch :
        (fun (x : {x : R2 d // σ x = k}) (c : C2 d) => M2 d x.val c)
          =
        (fun (x : {x : R2 d // σ x = k}) (c : C2 d) =>
          M1T d x.val.2 (S2fam d c α)) := by
      funext x c
      have hxα : α = x.val.1 := by
        dsimp [α, σ] at x ⊢
        simpa using (congrArg (Fin.cast hqpow.symm) x.property).symm
      rw [M2_apply, M1T, ← hxα]
    have hswap : D (M1T d) = D (M1 d) := by
      simpa [M1T] using comp_transpose (M1 d)
    simpa [hbranch, hswap] using hmap
  dsimp [Qlog] at hpart
  rw [hclog] at hpart
  omega

/-- Copy-count bridge for the Stage-2 hard seed.  Under the expected large-`d`
gate `5 ≤ log t2`, the hard-seed copy count is `(9 * t2) / 16`. -/
theorem M2_hard_seed_copies_eq_nine_mul_t2_div_sixteen (d : ℕ)
    (hlogt : 5 ≤ Nat.log 2 (Params.t2 d)) :
    M2_hard_seed_copies d = (9 * Params.t2 d) / 16 := by
  let n := Nat.log 2 (Params.t2 d)
  have ht : Params.t2 d = 2 ^ n := by
    simpa [n] using t2_eq_two_pow_log d
  have hsplit : 2 ^ n = 32 * 2 ^ (n - 5) := by
    have hn : n = 5 + (n - 5) := by omega
    rw [hn, pow_add]
    norm_num
  have hdiv :
      (9 * (32 * 2 ^ (n - 5))) / 16 = 18 * 2 ^ (n - 5) := by
    rw [show 9 * (32 * 2 ^ (n - 5)) = 16 * (18 * 2 ^ (n - 5)) by ring]
    rw [mul_comm 16 (18 * 2 ^ (n - 5))]
    exact Nat.mul_div_left _ (by norm_num : 0 < 16)
  calc
    M2_hard_seed_copies d = 18 * 2 ^ (n - 5) := by
      simp [M2_hard_seed_copies, Params.jSurplus, n]
    _ = (9 * (32 * 2 ^ (n - 5))) / 16 := hdiv.symm
    _ = (9 * 2 ^ n) / 16 := by rw [hsplit]
    _ = (9 * Params.t2 d) / 16 := by rw [ht]
-- CLAIM-END aux:m2-midlayer

-- CLAIM-BEGIN lem:M2-hard-seed
/-- Paper `lem:M2-hard-seed`, in the direct hard-seed form.  The two explicit
large-`d` gates are the generic hard-seed threshold `m0 ≤ log t2` and the
copy-budget inequality `log t2 ≤ b1`; the latter is usually discharged from
the large-`d` checklist field `t2 ≤ 2^b1`. -/
theorem M2_hard_seed (d : ℕ) (hpow : IsPow2 d)
    (hlog256 : 256 ≤ Nat.log 2 d)
    (hm0_le : (Classical.choose
        (hard_seed.{0} Params.jSurplus (by norm_num [Params.jSurplus])
          Params.delta (by norm_num [Params.delta])
          (by norm_num [Params.delta])) : ℕ) ≤ Nat.log 2 (Params.t2 d))
    (hm_le_b1 : (Nat.log 2 (Params.t2 d) : ℝ) ≤ (Params.b1 d : ℝ)) :
    D (M1T d) + Nat.log 2 (Params.t2 d) ≤
      Dfamily (interlaceFun (M1T d) (M2_hard_seed_copies d))
        (bracketGE (C1 d) (R1 d) (M2_hard_seed_copies d)
          (M2_hard_seed_rowDensity d) (M2_hard_seed_columnDensity d)) := by
-- CLAIM-END lem:M2-hard-seed
  classical
  let HS :=
    hard_seed.{0} Params.jSurplus (by norm_num [Params.jSurplus])
      Params.delta (by norm_num [Params.delta]) (by norm_num [Params.delta])
  have hspec := Classical.choose_spec HS
  have hm0_le' : Classical.choose HS ≤ Nat.log 2 (Params.t2 d) := by
    simpa [HS] using hm0_le
  have hhard := hspec.2
  have hlog64 : 64 ≤ Nat.log 2 d := by omega
  have hrob : IsRobust (M1T d) Params.delta (Params.b1 d) := by
    simpa [M1T] using M1_robust d hpow hlog256
  have hb1 : (1 : ℝ) ≤ (Params.b1 d : ℝ) := by
    have hb1nat : 1 ≤ Params.b1 d := by
      unfold Params.b1
      omega
    exact_mod_cast hb1nat
  have hD3 : 3 ≤ D (M1T d) := by
    have hD := M1T_complexity d hpow hlog64
    have ha2 : 2 ≤ Params.a d := by
      obtain ⟨k, rfl⟩ := hpow
      have hk : 256 ≤ k := by simpa [log_two_pow] using hlog256
      have hlog2 : 2 ≤ Nat.log 2 (2 ^ k) := by
        rw [log_two_pow]
        omega
      have hlow : 2 * Nat.log 2 (2 ^ k) ^ 2 ≤ Params.q1 (2 ^ k) + 2 :=
        Params.le_q1_add_two (d := 2 ^ k) (by omega : 1 ≤ Nat.log 2 (2 ^ k))
      have h2a : Params.q1 (2 ^ k) + 2 = 2 ^ Params.a (2 ^ k) :=
        Params.q1_add_two_pow (by omega)
      rw [h2a] at hlow
      have hbig : (2 : ℕ) ^ 2 ≤ 2 ^ Params.a (2 ^ k) := by
        calc (2 : ℕ) ^ 2 = 4 := by norm_num
          _ ≤ 2 * Nat.log 2 (2 ^ k) ^ 2 := by nlinarith
          _ ≤ 2 ^ Params.a (2 ^ k) := hlow
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hbig
    rw [hD]
    omega
  have hmain := hhard (Nat.log 2 (Params.t2 d)) hm0_le'
    (C1 d) (R1 d) (M1T d) (Params.b1 d : ℝ) hrob hb1 hD3 hm_le_b1
  simpa [M2_hard_seed_copies, M2_hard_seed_rowDensity,
    M2_hard_seed_columnDensity, Params.jSurplus] using hmain

private theorem Dfamily_one_mono_column_stage2 {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] (f : X → Y → Bool) {x y₀ y : ℝ}
    (hx1 : x ≤ 1) (hy₀y : y₀ ≤ y) (hy1 : y ≤ 1)
    (hX : 1 ≤ Fintype.card X) :
    Dfamily (interlaceFun f 1) (bracketGE X Y 1 x y₀) ≤
      Dfamily (interlaceFun f 1) (bracketGE X Y 1 x y) := by
  classical
  have hsub : bracketGE X Y 1 x y ⊆ bracketGE X Y 1 x y₀ :=
    bracketGE.anti_mono_params 1 (le_refl x) hy₀y
  have hne : (bracketGE X Y 1 x y).Nonempty :=
    bracketGE.nonempty 1 x y hx1 hy1 hX
  exact Dfamily.anti_mono (interlaceFun f 1) hsub hne

private theorem LambdaGE_one_ge_D_of_robust_stage2 {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] (f : X → Y → Bool)
    {b y : ℝ} (hrob : IsRobust f Params.delta b) (hb0 : 0 ≤ b)
    (hylo : 1 / 2 + Params.delta ≤ y) (hyhi : y ≤ 1)
    (hX : 1 ≤ Fintype.card X) :
    D f ≤ LambdaGE f 1 ((2 : ℝ) ^ (-b)) y := by
  classical
  let x : ℝ := (2 : ℝ) ^ (-b)
  have hx1 : x ≤ 1 := by
    dsimp [x]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
    exact neg_nonpos.mpr hb0
  have htop_mono :
      Dfamily (interlaceFun f 1)
          (bracketGE X Y 1 x (1 / 2 + Params.delta)) ≤
        Dfamily (interlaceFun f 1) (bracketGE X Y 1 x y) :=
    Dfamily_one_mono_column_stage2 f hx1 hylo hyhi hX
  have htop :
      D f ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x y) := by
    exact le_trans hrob.r2 htop_mono
  have hy2lo : 1 / 4 + Params.delta / 2 ≤ y / 2 := by linarith
  have hy2hi : y / 2 ≤ 1 := by linarith
  have hmid_mono :
      Dfamily (interlaceFun f 1)
          (bracketGE X Y 1 x (1 / 4 + Params.delta / 2)) ≤
        Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (y / 2)) :=
    Dfamily_one_mono_column_stage2 f hx1 hy2lo hy2hi hX
  have hmid_base :
      D f ≤ 1 + Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (1 / 4 + Params.delta / 2)) := by
    have hz : (D f : ℤ) - 1 ≤
        (Dfamily (interlaceFun f 1)
          (bracketGE X Y 1 x (1 / 4 + Params.delta / 2)) : ℤ) := hrob.r4
    have hz' : (D f : ℤ) ≤
        (1 + Dfamily (interlaceFun f 1)
          (bracketGE X Y 1 x (1 / 4 + Params.delta / 2)) : ℕ) := by
      omega
    exact_mod_cast hz'
  have hmid :
      D f ≤ 1 + Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (y / 2)) := by
    exact le_trans hmid_base (Nat.add_le_add_left hmid_mono 1)
  have hy4lo : 1 / 8 + Params.delta / 4 ≤ y / 4 := by linarith
  have hy4hi : y / 4 ≤ 1 := by linarith
  have hlow_mono :
      Dfamily (interlaceFun f 1)
          (bracketGE X Y 1 x (1 / 8 + Params.delta / 4)) ≤
        Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (y / 4)) :=
    Dfamily_one_mono_column_stage2 f hx1 hy4lo hy4hi hX
  have hlow_base :
      D f ≤ 2 + Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (1 / 8 + Params.delta / 4)) := by
    have hz : (D f : ℤ) - 2 ≤
        (Dfamily (interlaceFun f 1)
          (bracketGE X Y 1 x (1 / 8 + Params.delta / 4)) : ℤ) := hrob.r3
    have hz' : (D f : ℤ) ≤
        (2 + Dfamily (interlaceFun f 1)
          (bracketGE X Y 1 x (1 / 8 + Params.delta / 4)) : ℕ) := by
      omega
    exact_mod_cast hz'
  have hlow :
      D f ≤ 2 + Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (y / 4)) := by
    exact le_trans hlow_base (Nat.add_le_add_left hlow_mono 2)
  unfold LambdaGE
  exact le_min htop (le_min hmid hlow)

-- CLAIM-BEGIN aux:m2-clr-discharge
/-- Stage-2 residual column-loss discharge from the robust three-rung ladder.
The remaining explicit gate is the App-C density window for every residual
loss consumed by clause (ii). -/
theorem M2_column_loss_resilient' (d : ℕ) (hpow : IsPow2 d)
    (hlog256 : 256 ≤ Nat.log 2 d)
    (hy_le_one : M1_stage2_terminal_density d ≤ 1)
    (hrowTerm : 9 * Params.t1 d ≤
      16 * ⌈(Fintype.card (R1 d) : ℝ) * M1_stage2_terminal_density d⌉₊)
    (hcolTerm : (2 : ℝ) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : ℤ))
        * (Fintype.card (C1 d) : ℝ) ≤
      (⌈(Fintype.card (C1 d) : ℝ) *
        ((2 : ℝ) ^ (-(Params.b1 d : ℤ)))⌉₊ : ℝ))
    (hresidual_density : ∀ c ≤ M2_T d + D (M1T d),
      1 / 2 + Params.delta ≤
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c ∧
        yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c ≤ 1) :
    IsColumnLossResilient (M1T d) (Params.b1 d : ℝ)
      (epsQT (Params.q2 d) (Params.t2 d))
      (Nat.log 2 (Params.q2 d)) (M2_T d) (Params.h2 d) := by
  classical
  have hlog64 : 64 ≤ Nat.log 2 d := by omega
  refine M2_column_loss_resilient d hpow hlog64 hy_le_one hrowTerm hcolTerm ?_
  intro k hk c hc
  have hrob : IsRobust (M1T d) Params.delta (Params.b1 d) := by
    simpa [M1T] using M1_robust d hpow hlog256
  have hb0 : (0 : ℝ) ≤ (Params.b1 d : ℝ) := by positivity
  have hCcard : 1 ≤ Fintype.card (C1 d) := by
    have hchk : Params.t1 d ≤ Params.q1 d + 5 :=
      Params.t1_le_q1_add_five hlog64
    simpa [C1, Fintype.card_fin] using L1_pos d hchk
  have hcD : c ≤ M2_T d + D (M1T d) := by omega
  obtain ⟨hylo, hyhi⟩ := hresidual_density c hcD
  have hLamD :
      D (M1T d) ≤
        LambdaGE (M1T d) 1 ((2 : ℝ) ^ (-(Params.b1 d : ℝ)))
          (yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c) :=
    LambdaGE_one_ge_D_of_robust_stage2 (M1T d) hrob hb0 hylo hyhi hCcard
  exact le_trans (Nat.sub_le (D (M1T d)) k) hLamD
-- CLAIM-END aux:m2-clr-discharge

-- CLAIM-BEGIN cor:M2-complexity
/-- Paper `cor:M2-complexity`: the exact Stage-2 complexity.  The lower bound
is assembled through `localized_extension` from `M2_hard_seed` and the
column-loss corollary above. The explicit residual gates are the numerical
Appendix-C comparisons required at this use site. -/
theorem M2_complexity (d : ℕ) (hpow : IsPow2 d)
    (hlog256 : 256 ≤ Nat.log 2 d)
    (hlarge : Checklist d)
    (hm0_le : (Classical.choose
        (hard_seed.{0} Params.jSurplus (by norm_num [Params.jSurplus])
          Params.delta (by norm_num [Params.delta])
          (by norm_num [Params.delta])) : ℕ) ≤ Nat.log 2 (Params.t2 d))
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d))
    (hp1 : 2 ^ M2_T d ≤ 2 * M2_hard_seed_copies d)
    (hp2 : M2_hard_seed_copies d ≤ 2 ^ M2_T d)
    (hxseed_le_one : M2_hard_seed_rowDensity d ≤ 1)
    (hrow_threshold :
      ⌈(2 : ℝ) ^ (Nat.log 2 (Params.r2 d) : ℕ) *
        M2_hard_seed_rowDensity d * (Fintype.card (C1 d) : ℝ)⌉₊
          ≤ Fintype.card (C1 d))
    (hseed_bridge : M2_hard_seed_columnDensity d ≤
      Params.h2 d *
        (2 : ℝ) ^ (-((M2_T d + D (M1T d) : ℕ) : ℝ)) /
          (1 + epsQT (Params.q2 d) (Params.t2 d)))
    (hy_le_one : M1_stage2_terminal_density d ≤ 1)
    (hrowTerm : 9 * Params.t1 d ≤
      16 * ⌈(Fintype.card (R1 d) : ℝ) * M1_stage2_terminal_density d⌉₊)
    (hcolTerm : (2 : ℝ) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : ℤ))
        * (Fintype.card (C1 d) : ℝ) ≤
      (⌈(Fintype.card (C1 d) : ℝ) *
        ((2 : ℝ) ^ (-(Params.b1 d : ℤ)))⌉₊ : ℝ))
    (hresidual_density : ∀ c ≤ M2_T d + D (M1T d),
      1 / 2 + Params.delta ≤
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c ∧
        yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c ≤ 1) :
    D (M2 d) = D (M1 d) + Nat.log 2 (Params.q2 d) := by
-- CLAIM-END cor:M2-complexity
  classical
  let T : ℕ := M2_T d
  let R : ℕ := Nat.log 2 (Params.r2 d)
  let ε : ℝ := epsQT (Params.q2 d) (Params.t2 d)
  have hlog64 : 64 ≤ Nat.log 2 d := by omega
  have hqcast : 2 ^ (R + T) = Params.q2 d := by
    calc
      2 ^ (R + T) = 2 ^ R * 2 ^ T := by rw [pow_add]
      _ = Params.r2 d * Params.t2 d := by
        dsimp [R, T]
        rw [← hr2pow, ← t2_eq_two_pow_M2_T d]
      _ = Params.q2 d := hlarge.q2_eq.symm
  have hQeq : R + T = Nat.log 2 (Params.q2 d) := by
    rw [← hqcast, log_two_pow]
  have hlogt_eq_T : Nat.log 2 (Params.t2 d) = T := by
    dsimp [T]
    rw [t2_eq_two_pow_M2_T, log_two_pow]
  have hm_le_b1 : (Nat.log 2 (Params.t2 d) : ℝ) ≤ (Params.b1 d : ℝ) := by
    have hpowle : 2 ^ Nat.log 2 (Params.t2 d) ≤ 2 ^ Params.b1 d := by
      rw [← t2_eq_two_pow_log d]
      exact hlarge.t2_le_pow_b1
    exact_mod_cast (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpowle
  have hb : (1 : ℝ) ≤ (Params.b1 d : ℝ) := by
    have hb1nat : 1 ≤ Params.b1 d := by
      unfold Params.b1
      omega
    exact_mod_cast hb1nat
  have hTb : (T : ℝ) ≤ (Params.b1 d : ℝ) := by
    simpa [hlogt_eq_T] using hm_le_b1
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact epsQT_pos (Params.q2_pos d) (Params.t2_pos d)
  have hεnonneg : 0 ≤ ε := le_of_lt hεpos
  let S' : Fin (L2 d) → Fin (2 ^ (R + T)) → R1 d :=
    fun j γ => S2fam d j (Fin.cast hqcast γ)
  have hSbase : IsBalancedFamily (Params.t2 d) (S2fam d) ε := by
    dsimp [ε]
    exact S2fam_balanced d hlarge.t2_le_q2 hlarge.one_le_q1
  have hcast_inj : Function.Injective (fun γ : Fin (2 ^ (R + T)) => Fin.cast hqcast γ) := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg (fun z : Fin (Params.q2 d) => z.val) hab
    simpa using hv
  have hSproj := hSbase.projection (fun γ : Fin (2 ^ (R + T)) => Fin.cast hqcast γ) hcast_inj
  have hS : IsBalancedFamily (2 ^ T) S' ε := by
    simpa [S', T, t2_eq_two_pow_M2_T d] using hSproj
  have hres0 := M2_column_loss_resilient' d hpow hlog256
    hy_le_one hrowTerm hcolTerm hresidual_density
  have hres : IsColumnLossResilient (M1T d) (Params.b1 d : ℝ) ε (R + T) T
      (Params.h2 d) := by
    simpa [ε, T, hQeq] using hres0
  have hseed0 := M2_hard_seed d hpow hlog256 hm0_le hm_le_b1
  have hseedbd : D (M1T d) + T ≤
      Dfamily (interlaceFun (M1T d) (M2_hard_seed_copies d))
        (bracketGE (C1 d) (R1 d) (M2_hard_seed_copies d)
          (M2_hard_seed_rowDensity d) (M2_hard_seed_columnDensity d)) := by
    simpa [hlogt_eq_T] using hseed0
  have hx1 : (2 : ℝ) ^ (-(Params.b1 d : ℝ)) ≤ M2_hard_seed_rowDensity d := by
    unfold M2_hard_seed_rowDensity
    have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 (Params.t2 d) : ℕ) :=
      one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hnonneg : 0 ≤ (2 : ℝ) ^ (-(Params.b1 d : ℝ)) := by positivity
    calc
      (2 : ℝ) ^ (-(Params.b1 d : ℝ))
          = 1 * (2 : ℝ) ^ (-(Params.b1 d : ℝ)) := by ring
      _ ≤ (2 : ℝ) ^ (Nat.log 2 (Params.t2 d) : ℕ) *
          (2 : ℝ) ^ (-(Params.b1 d : ℝ)) :=
            mul_le_mul_of_nonneg_right hpow1 hnonneg
  have hh0 : 0 < Params.h2 d := Params.h2_pos
  have hh1 : Params.h2 d ≤ 1 := by
    unfold Params.h2
    rw [two_zpow_neg_nat_eq_rpow_neg_nat_stage2 (Params.b2 d)]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
    exact neg_nonpos.mpr (Nat.cast_nonneg _)
  have hs0 : 0 < M2_hard_seed_columnDensity d := by
    unfold M2_hard_seed_columnDensity
    positivity
  have hs1 : M2_hard_seed_columnDensity d ≤ 1 := by
    unfold M2_hard_seed_columnDensity
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
    exact neg_nonpos.mpr (by positivity)
  let Rs : Finset (Fin (2 ^ (R + T)) × C1 d) := Finset.univ
  let Cs : Finset (Fin (L2 d)) := Finset.univ
  have hQcard_le : 2 ^ R * M2_hard_seed_copies d ≤ 2 ^ (R + T) := by
    calc
      2 ^ R * M2_hard_seed_copies d ≤ 2 ^ R * 2 ^ T := by
        exact Nat.mul_le_mul_left (2 ^ R) (by simpa [T] using hp2)
      _ = 2 ^ (R + T) := by rw [pow_add]
  have hQcard_le_univ : 2 ^ R * M2_hard_seed_copies d ≤
      (Finset.univ : Finset (Fin (2 ^ (R + T)))).card := by
    simpa [Finset.card_univ, Fintype.card_fin] using hQcard_le
  obtain ⟨Qs, _hQsub, hQcard⟩ :=
    Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin (2 ^ (R + T))))) hQcard_le_univ
  have hRs : ∃ Qs : Finset (Fin (2 ^ (R + T))),
      Qs.card = 2 ^ R * M2_hard_seed_copies d ∧
        IsEquipartitionedGE Rs Qs
          ⌈(2 : ℝ) ^ (R : ℕ) *
            M2_hard_seed_rowDensity d * (Fintype.card (C1 d) : ℝ)⌉₊ := by
    refine ⟨Qs, hQcard, ?_⟩
    intro q hq
    dsimp [Rs]
    have hfilter :
        (Finset.univ : Finset (Fin (2 ^ (R + T)) × C1 d)).filter
            (fun p => p.1 = q)
          = ({q} : Finset (Fin (2 ^ (R + T)))).product
              (Finset.univ : Finset (C1 d)) := by
      ext p
      rcases p with ⟨i, x⟩
      simp [eq_comm]
    rw [hfilter]
    simpa [R] using hrow_threshold
  have hCs : Params.h2 d * (2 : ℝ) ^ (-((0 : ℕ) : ℝ)) * (L2 d : ℝ) ≤
      (Cs.card : ℝ) := by
    have hscale : Params.h2 d * (2 : ℝ) ^ (-((0 : ℕ) : ℝ)) ≤ 1 := by
      norm_num
      exact hh1
    dsimp [Cs]
    simpa [Fintype.card_fin] using
      mul_le_of_le_one_left (by positivity : 0 ≤ (L2 d : ℝ)) hscale
  have hmain : D (M1T d) + (R + T) ≤
      D (subgame (relaxedInterlace (M1T d) S') Rs Cs) :=
    localized_extension (X := C1 d) (Y := R1 d) (f := M1T d)
      (b := (Params.b1 d : ℝ)) (ε := ε) hb hεnonneg T R hTb
      (S := S') hS (M2_hard_seed_copies d)
      (xseed := M2_hard_seed_rowDensity d) (h := Params.h2 d)
      (hseed := M2_hard_seed_columnDensity d)
      hx1 hxseed_le_one hh0 hh1 hs0 hs1 (by simpa [T] using hp1)
      (by simpa [T] using hp2) hres hseedbd (by simpa [T, ε] using hseed_bridge)
      0 R (by omega) (le_refl R) Rs Cs hRs hCs
  have hsub_le : D (subgame (relaxedInterlace (M1T d) S') Rs Cs) ≤
      D (relaxedInterlace (M1T d) S') :=
    D_subgame_le (relaxedInterlace (M1T d) S') Rs Cs
  have hrel_lower : D (M1T d) + (R + T) ≤ D (relaxedInterlace (M1T d) S') :=
    le_trans hmain hsub_le
  let eRows : R2 d ≃ Fin (2 ^ (R + T)) × C1 d :=
    Equiv.prodCongr (finCongr hqcast.symm) (Equiv.refl (C1 d))
  have hgame :
      (fun a b => relaxedInterlace (M1T d) S' (eRows a) b) = M2 d := by
    funext a b
    simp [relaxedInterlace, S', M2, M1T, eRows]
  have hDinv := D_equiv_invariance (relaxedInterlace (M1T d) S')
    eRows (Equiv.refl (Fin (L2 d)))
  have hDrel_eq : D (relaxedInterlace (M1T d) S') = D (M2 d) := by
    have hgame' :
        (fun a b => relaxedInterlace (M1T d) S' (eRows a)
          ((Equiv.refl (Fin (L2 d))) b)) = M2 d := by
      simpa using hgame
    rw [hgame'] at hDinv
    exact hDinv.symm
  have hlowerT : D (M1T d) + (R + T) ≤ D (M2 d) := by
    rwa [hDrel_eq] at hrel_lower
  have hswap : D (M1T d) = D (M1 d) := by
    simpa [M1T] using comp_transpose (M1 d)
  have hlower : D (M1 d) + Nat.log 2 (Params.q2 d) ≤ D (M2 d) := by
    simpa [hswap, hQeq] using hlowerT
  exact le_antisymm (M2_upper_bound d hlarge.clog_q2_eq) hlower

-- CLAIM-BEGIN lem:M2Separation
/-- Paper `lem:M2Separation`, as the live `relaxed_separation` theorem
instantiated at the Stage-2 relaxed interlace.  The statement keeps the same
explicit arithmetic gates as `M2_complexity`; the extra named gates are the
separation-only side conditions and the monotone column-loss upgrade from the
certified `h2` density to the `h = 1` density used by the paper. -/
theorem M2_separation (d : ℕ) (hpow : IsPow2 d)
    (hlog256 : 256 ≤ Nat.log 2 d)
    (hlarge : Checklist d)
    (hm0_le : (Classical.choose
        (hard_seed.{0} Params.jSurplus (by norm_num [Params.jSurplus])
          Params.delta (by norm_num [Params.delta])
          (by norm_num [Params.delta])) : ℕ) ≤ Nat.log 2 (Params.t2 d))
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d))
    (hp1 : 2 ^ M2_T d ≤ 2 * M2_hard_seed_copies d)
    (hp2 : M2_hard_seed_copies d ≤ 2 ^ M2_T d)
    (hxseed_le_one : M2_hard_seed_rowDensity d ≤ 1)
    (hrow_threshold :
      ⌈(2 : ℝ) ^ (Nat.log 2 (Params.r2 d) : ℕ) *
        M2_hard_seed_rowDensity d * (Fintype.card (C1 d) : ℝ)⌉₊
          ≤ Fintype.card (C1 d))
    (hseed_bridge : M2_hard_seed_columnDensity d ≤
      Params.h2 d *
        (2 : ℝ) ^ (-((M2_T d + D (M1T d) : ℕ) : ℝ)) /
          (1 + epsQT (Params.q2 d) (Params.t2 d)))
    (hy_le_one : M1_stage2_terminal_density d ≤ 1)
    (hrowTerm : 9 * Params.t1 d ≤
      16 * ⌈(Fintype.card (R1 d) : ℝ) * M1_stage2_terminal_density d⌉₊)
    (hcolTerm : (2 : ℝ) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : ℤ))
        * (Fintype.card (C1 d) : ℝ) ≤
      (⌈(Fintype.card (C1 d) : ℝ) *
        ((2 : ℝ) ^ (-(Params.b1 d : ℤ)))⌉₊ : ℝ))
    (hresidual_density : ∀ c ≤ M2_T d + D (M1T d),
      1 / 2 + Params.delta ≤
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c ∧
        yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c ≤ 1)
    (hqcast : 2 ^ (Nat.log 2 (Params.r2 d) + M2_T d) = Params.q2 d)
    (hres_one : IsColumnLossResilient (M1T d) (Params.b1 d : ℝ)
      (epsQT (Params.q2 d) (Params.t2 d))
      (Nat.log 2 (Params.q2 d)) (M2_T d) 1)
    (hxseed_le_inv_r : M2_hard_seed_rowDensity d ≤
      (2 : ℝ) ^ (-(Nat.log 2 (Params.r2 d) : ℝ)))
    (hseed_bridge_one : M2_hard_seed_columnDensity d ≤
      (1 : ℝ) *
        (2 : ℝ) ^ (-((M2_T d + D (M1T d) : ℕ) : ℝ)) /
          (1 + epsQT (Params.q2 d) (Params.t2 d)))
    (hdelta_sep : Params.delta ≤ 1 / Real.sqrt 2 - 1 / 2)
    (hT1 : 1 ≤ M2_T d)
    (hband : 2 * (1 / 2 + Params.delta) ^ 2 ≤
      (1 : ℝ) / (1 + epsQT (Params.q2 d) (Params.t2 d)))
    (hgap :
      2 ^ (Nat.log 2 (Params.r2 d) + M2_T d) *
        ⌈(2 : ℝ) ^ (1 - (Params.b1 d : ℝ)) *
          (Fintype.card (C1 d) : ℝ)⌉₊ < Fintype.card (C1 d))
    (P : Protocol
      {a // a ∈
        (Finset.univ :
          Finset (Fin (2 ^ (Nat.log 2 (Params.r2 d) + M2_T d)) × C1 d))}
      {c // c ∈ (Finset.univ : Finset (C2 d))} Bool)
    (hP : P.Computes (subgame
      (relaxedInterlace (M1T d)
        (fun j γ => S2fam d j (Fin.cast hqcast γ)))
      (Finset.univ :
        Finset (Fin (2 ^ (Nat.log 2 (Params.r2 d) + M2_T d)) × C1 d))
      (Finset.univ : Finset (C2 d))))
    (hcost : P.cost ≤ D (M2 d)) :
    Protocol.FirstKRowBitsOn
        (Finset.univ :
          Finset {a // a ∈
            (Finset.univ :
              Finset (Fin (2 ^ (Nat.log 2 (Params.r2 d) + M2_T d)) × C1 d))})
        (Finset.univ : Finset {c // c ∈ (Finset.univ : Finset (C2 d))})
        (Nat.log 2 (Params.r2 d) + M2_T d) P
    ∧ NoWasteConclusion
        (Finset.univ : Finset (Fin (2 ^ (Nat.log 2 (Params.r2 d) + M2_T d))))
        (Finset.univ :
          Finset (Fin (2 ^ (Nat.log 2 (Params.r2 d) + M2_T d)) × C1 d))
        (Protocol.prefixLabelFinQ
          (Finset.univ :
            Finset (Fin (2 ^ (Nat.log 2 (Params.r2 d) + M2_T d)) × C1 d)) P)
        (Fintype.card (C1 d))
        ⌈(2 : ℝ) ^ (1 - (Params.b1 d : ℝ)) *
          (Fintype.card (C1 d) : ℝ)⌉₊ := by
-- CLAIM-END lem:M2Separation
  classical
  let T : ℕ := M2_T d
  let R : ℕ := Nat.log 2 (Params.r2 d)
  let ε : ℝ := epsQT (Params.q2 d) (Params.t2 d)
  let S : Fin (L2 d) → Fin (2 ^ (R + T)) → R1 d :=
    fun j γ => S2fam d j (Fin.cast (by simpa [R, T] using hqcast) γ)
  have hQeq : R + T = Nat.log 2 (Params.q2 d) := by
    rw [← hqcast]
    simp [R, T]
  have hlog64 : 64 ≤ Nat.log 2 d := by omega
  have hm_le_b1 : (Nat.log 2 (Params.t2 d) : ℝ) ≤ (Params.b1 d : ℝ) := by
    have hpowle : 2 ^ Nat.log 2 (Params.t2 d) ≤ 2 ^ Params.b1 d := by
      rw [← t2_eq_two_pow_log d]
      exact hlarge.t2_le_pow_b1
    exact_mod_cast (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpowle
  have hb : (1 : ℝ) ≤ (Params.b1 d : ℝ) := by
    have hb1nat : 1 ≤ Params.b1 d := by
      unfold Params.b1
      omega
    exact_mod_cast hb1nat
  have hlogt_eq_T : Nat.log 2 (Params.t2 d) = T := by
    dsimp [T]
    rw [t2_eq_two_pow_M2_T, log_two_pow]
  have hTb : (T : ℝ) ≤ (Params.b1 d : ℝ) := by
    simpa [hlogt_eq_T] using hm_le_b1
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact epsQT_pos (Params.q2_pos d) (Params.t2_pos d)
  have hεnonneg : 0 ≤ ε := le_of_lt hεpos
  have hSbase : IsBalancedFamily (Params.t2 d) (S2fam d) ε := by
    dsimp [ε]
    exact S2fam_balanced d hlarge.t2_le_q2 hlarge.one_le_q1
  have hcast_inj :
      Function.Injective
        (fun γ : Fin (2 ^ (R + T)) =>
          Fin.cast (by simpa [R, T] using hqcast) γ) := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg (fun z : Fin (Params.q2 d) => z.val) hab
    simpa using hv
  have hSproj :=
    hSbase.projection
      (fun γ : Fin (2 ^ (R + T)) =>
        Fin.cast (by simpa [R, T] using hqcast) γ) hcast_inj
  have hS : IsBalancedFamily (2 ^ T) S ε := by
    simpa [S, T, t2_eq_two_pow_M2_T d] using hSproj
  have hseed0 := M2_hard_seed d hpow hlog256 hm0_le hm_le_b1
  have hseedbd : D (M1T d) + T ≤
      Dfamily (interlaceFun (M1T d) (M2_hard_seed_copies d))
        (bracketGE (C1 d) (R1 d) (M2_hard_seed_copies d)
          (M2_hard_seed_rowDensity d) (M2_hard_seed_columnDensity d)) := by
    simpa [hlogt_eq_T] using hseed0
  have hx1 : (2 : ℝ) ^ (-(Params.b1 d : ℝ)) ≤ M2_hard_seed_rowDensity d := by
    unfold M2_hard_seed_rowDensity
    have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 (Params.t2 d) : ℕ) :=
      one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hnonneg : 0 ≤ (2 : ℝ) ^ (-(Params.b1 d : ℝ)) := by positivity
    calc
      (2 : ℝ) ^ (-(Params.b1 d : ℝ))
          = 1 * (2 : ℝ) ^ (-(Params.b1 d : ℝ)) := by ring
      _ ≤ (2 : ℝ) ^ (Nat.log 2 (Params.t2 d) : ℕ) *
          (2 : ℝ) ^ (-(Params.b1 d : ℝ)) :=
            mul_le_mul_of_nonneg_right hpow1 hnonneg
  have hs0 : 0 < M2_hard_seed_columnDensity d := by
    unfold M2_hard_seed_columnDensity
    positivity
  have hs1 : M2_hard_seed_columnDensity d ≤ 1 := by
    unfold M2_hard_seed_columnDensity
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
    exact neg_nonpos.mpr (by positivity)
  have hD : 2 ≤ D (M1T d) := by
    have hcomp := M1T_complexity d hpow hlog64
    rw [hcomp]
    have ha : 2 ≤ Params.a d := hlarge.a_ge_two
    omega
  have hrob : IsRobust (M1T d) Params.delta (Params.b1 d) := by
    simpa [M1T] using M1_robust d hpow hlog256
  have hres : IsColumnLossResilient (M1T d) (Params.b1 d : ℝ) ε (R + T) T 1 := by
    simpa [ε, T, R, hQeq] using hres_one
  have hM2comp := M2_complexity d hpow hlog256 hlarge hm0_le hr2pow hp1 hp2
    hxseed_le_one hrow_threshold hseed_bridge hy_le_one hrowTerm hcolTerm
    hresidual_density
  have hbudget : P.cost ≤ D (M1T d) + (R + T) := by
    have hcost' := hcost
    rw [hM2comp] at hcost'
    have hswap : D (M1T d) = D (M1 d) := by
      simpa [M1T] using comp_transpose (M1 d)
    rw [hswap]
    simpa [hQeq] using hcost'
  have hCuniv : (1 : ℝ) * (L2 d : ℝ) ≤
      ((Finset.univ : Finset (C2 d)).card : ℝ) := by
    simp [C2]
  simpa [S, R, T, ε] using
    relaxed_separation (f := M1T d) (δ := Params.delta)
      (b := (Params.b1 d : ℝ)) (ε := ε) hb hεnonneg T R hTb
      (S := S) hS (M2_hard_seed_copies d)
      (xseed := M2_hard_seed_rowDensity d) (h := (1 : ℝ))
      (hseed := M2_hard_seed_columnDensity d)
      hx1 hxseed_le_inv_r (by norm_num) (by norm_num) hs0 hs1
      (by simpa [T] using hp1) (by simpa [T] using hp2)
      hres hseedbd (by simpa [T, ε] using hseed_bridge_one)
      hrob (by norm_num [Params.delta]) hdelta_sep hD hT1
      (by simpa [ε] using hband) (by simpa [R, T] using hgap)
      (Finset.univ : Finset (C2 d)) hCuniv P hP hbudget

private def M2_robust_balance_gate (d R'e : ℕ) (β : ℝ) : Prop :=
  2 ^ R'e * M2_hard_seed_copies d ≤
    ⌈(Params.q2 d : ℝ) *
      (β - (2 : ℝ) ^ R'e * M2_hard_seed_rowDensity d) /
        (1 - (2 : ℝ) ^ R'e * M2_hard_seed_rowDensity d)⌉₊

private theorem M2_family_lower_from_localized (d : ℕ) (hpow : IsPow2 d)
    (hlog256 : 256 ≤ Nat.log 2 d)
    (hlarge : Checklist d)
    (hm0_le : (Classical.choose
        (hard_seed.{0} Params.jSurplus (by norm_num [Params.jSurplus])
          Params.delta (by norm_num [Params.delta])
          (by norm_num [Params.delta])) : ℕ) ≤ Nat.log 2 (Params.t2 d))
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d))
    (hp1 : 2 ^ M2_T d ≤ 2 * M2_hard_seed_copies d)
    (hp2 : M2_hard_seed_copies d ≤ 2 ^ M2_T d)
    (hxseed_le_one : M2_hard_seed_rowDensity d ≤ 1)
    (hseed_bridge : M2_hard_seed_columnDensity d ≤
      Params.h2 d *
        (2 : ℝ) ^ (-((M2_T d + D (M1T d) : ℕ) : ℝ)) /
          (1 + epsQT (Params.q2 d) (Params.t2 d)))
    (hy_le_one : M1_stage2_terminal_density d ≤ 1)
    (hrowTerm : 9 * Params.t1 d ≤
      16 * ⌈(Fintype.card (R1 d) : ℝ) * M1_stage2_terminal_density d⌉₊)
    (hcolTerm : (2 : ℝ) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : ℤ))
        * (Fintype.card (C1 d) : ℝ) ≤
      (⌈(Fintype.card (C1 d) : ℝ) *
        ((2 : ℝ) ^ (-(Params.b1 d : ℤ)))⌉₊ : ℝ))
    (hresidual_density : ∀ c ≤ M2_T d + D (M1T d),
      1 / 2 + Params.delta ≤
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c ∧
        yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c ≤ 1)
    {β : ℝ} {R'e : ℕ}
    (hR'eR : R'e ≤ Nat.log 2 (Params.r2 d))
    (hβpos : 0 < β) (hβlt1 : β < 1)
    (hxβ : (2 : ℝ) ^ R'e * M2_hard_seed_rowDensity d ≤ β)
    (hbalance : M2_robust_balance_gate d R'e β) :
    D (M1T d) + (R'e + M2_T d) ≤
      Dfamily (interlaceFun (M2 d) 1)
        (bracketGE (R2 d) (C2 d) 1 β (Params.h2 d)) := by
  classical
  let T : ℕ := M2_T d
  let R : ℕ := Nat.log 2 (Params.r2 d)
  let ε : ℝ := epsQT (Params.q2 d) (Params.t2 d)
  let xloc : ℝ := (2 : ℝ) ^ R'e * M2_hard_seed_rowDensity d
  have hlog64 : 64 ≤ Nat.log 2 d := by omega
  have hqcast : 2 ^ (R + T) = Params.q2 d := by
    calc
      2 ^ (R + T) = 2 ^ R * 2 ^ T := by rw [pow_add]
      _ = Params.r2 d * Params.t2 d := by
        dsimp [R, T]
        rw [← hr2pow, ← t2_eq_two_pow_M2_T d]
      _ = Params.q2 d := hlarge.q2_eq.symm
  have hQeq : R + T = Nat.log 2 (Params.q2 d) := by
    rw [← hqcast, log_two_pow]
  have hlogt_eq_T : Nat.log 2 (Params.t2 d) = T := by
    dsimp [T]
    rw [t2_eq_two_pow_M2_T, log_two_pow]
  have hm_le_b1 : (Nat.log 2 (Params.t2 d) : ℝ) ≤ (Params.b1 d : ℝ) := by
    have hpowle : 2 ^ Nat.log 2 (Params.t2 d) ≤ 2 ^ Params.b1 d := by
      rw [← t2_eq_two_pow_log d]
      exact hlarge.t2_le_pow_b1
    exact_mod_cast (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpowle
  have hb : (1 : ℝ) ≤ (Params.b1 d : ℝ) := by
    have hb1nat : 1 ≤ Params.b1 d := by
      unfold Params.b1
      omega
    exact_mod_cast hb1nat
  have hTb : (T : ℝ) ≤ (Params.b1 d : ℝ) := by
    simpa [hlogt_eq_T] using hm_le_b1
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact epsQT_pos (Params.q2_pos d) (Params.t2_pos d)
  have hεnonneg : 0 ≤ ε := le_of_lt hεpos
  let S' : Fin (L2 d) → Fin (2 ^ (R + T)) → R1 d :=
    fun j γ => S2fam d j (Fin.cast hqcast γ)
  have hSbase : IsBalancedFamily (Params.t2 d) (S2fam d) ε := by
    dsimp [ε]
    exact S2fam_balanced d hlarge.t2_le_q2 hlarge.one_le_q1
  have hcast_inj : Function.Injective (fun γ : Fin (2 ^ (R + T)) => Fin.cast hqcast γ) := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg (fun z : Fin (Params.q2 d) => z.val) hab
    simpa using hv
  have hSproj := hSbase.projection (fun γ : Fin (2 ^ (R + T)) => Fin.cast hqcast γ) hcast_inj
  have hS : IsBalancedFamily (2 ^ T) S' ε := by
    simpa [S', T, t2_eq_two_pow_M2_T d] using hSproj
  have hres0 := M2_column_loss_resilient' d hpow hlog256
    hy_le_one hrowTerm hcolTerm hresidual_density
  have hres : IsColumnLossResilient (M1T d) (Params.b1 d : ℝ) ε (R + T) T
      (Params.h2 d) := by
    simpa [ε, T, hQeq] using hres0
  have hseed0 := M2_hard_seed d hpow hlog256 hm0_le hm_le_b1
  have hseedbd : D (M1T d) + T ≤
      Dfamily (interlaceFun (M1T d) (M2_hard_seed_copies d))
        (bracketGE (C1 d) (R1 d) (M2_hard_seed_copies d)
          (M2_hard_seed_rowDensity d) (M2_hard_seed_columnDensity d)) := by
    simpa [hlogt_eq_T] using hseed0
  have hx1 : (2 : ℝ) ^ (-(Params.b1 d : ℝ)) ≤ M2_hard_seed_rowDensity d := by
    unfold M2_hard_seed_rowDensity
    have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 (Params.t2 d) : ℕ) :=
      one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hnonneg : 0 ≤ (2 : ℝ) ^ (-(Params.b1 d : ℝ)) := by positivity
    calc
      (2 : ℝ) ^ (-(Params.b1 d : ℝ))
          = 1 * (2 : ℝ) ^ (-(Params.b1 d : ℝ)) := by ring
      _ ≤ (2 : ℝ) ^ (Nat.log 2 (Params.t2 d) : ℕ) *
          (2 : ℝ) ^ (-(Params.b1 d : ℝ)) :=
            mul_le_mul_of_nonneg_right hpow1 hnonneg
  have hh0 : 0 < Params.h2 d := Params.h2_pos
  have hh1 : Params.h2 d ≤ 1 := by
    unfold Params.h2
    rw [two_zpow_neg_nat_eq_rpow_neg_nat_stage2 (Params.b2 d)]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
    exact neg_nonpos.mpr (Nat.cast_nonneg _)
  have hs0 : 0 < M2_hard_seed_columnDensity d := by
    unfold M2_hard_seed_columnDensity
    positivity
  have hs1 : M2_hard_seed_columnDensity d ≤ 1 := by
    unfold M2_hard_seed_columnDensity
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
    exact neg_nonpos.mpr (by positivity)
  have hxloc_pos : 0 < xloc := by
    dsimp [xloc, M2_hard_seed_rowDensity]
    positivity
  have hxloc_lt_one : xloc < 1 := lt_of_le_of_lt hxβ hβlt1
  have hC1card_pos : 0 < Fintype.card (C1 d) := by
    simpa [C1, Fintype.card_fin] using L1_pos d hlarge.t1_le_q1_add_five
  have hR2card_pos : 0 < Fintype.card (R2 d) := by
    simpa [R2, C1, Fintype.card_prod, Fintype.card_fin] using
      Nat.mul_pos (Params.q2_pos d) hC1card_pos
  have hR2card : 1 ≤ Fintype.card (R2 d) := Nat.succ_le_of_lt hR2card_pos
  have hC2card : 1 ≤ Fintype.card (C2 d) := by
    simpa [C2, Fintype.card_fin] using
      L2_pos d hlarge.t2_le_q2 hlarge.one_le_q1
  have hbr_ne : (bracketGE (R2 d) (C2 d) 1 β (Params.h2 d)).Nonempty :=
    bracketGE.nonempty 1 β (Params.h2 d) (le_of_lt hβlt1) hh1 hR2card
  unfold Dfamily
  set Fam : Set ℕ :=
    { m : ℕ | ∃ RC ∈ bracketGE (R2 d) (C2 d) 1 β (Params.h2 d),
        m = D (subgame (interlaceFun (M2 d) 1) RC.1 RC.2) } with hFam
  change D (M1T d) + (R'e + M2_T d) ≤ sInf Fam
  have hFam_ne : Fam.Nonempty := by
    rcases hbr_ne with ⟨RC, hRC⟩
    exact ⟨D (subgame (interlaceFun (M2 d) 1) RC.1 RC.2), RC, hRC, rfl⟩
  have hmem := Nat.sInf_mem hFam_ne
  rcases hmem with ⟨RC, hRC, hRCeq⟩
  rw [hRCeq]
  rcases hRC with ⟨hRows, hCols⟩
  let eRows : R2 d ≃ Fin (2 ^ (R + T)) × C1 d :=
    Equiv.prodCongr (finCongr hqcast.symm) (Equiv.refl (C1 d))
  let rowMap : Fin 1 × R2 d → Fin (2 ^ (R + T)) × C1 d := fun p => eRows p.2
  let colMap : (Fin 1 → C2 d) → Fin (L2 d) := fun c => c 0
  let Rs : Finset (Fin (2 ^ (R + T)) × C1 d) := RC.1.image rowMap
  let Cs : Finset (Fin (L2 d)) := RC.2.image colMap
  have hrowMap_inj : Function.Injective rowMap := by
    intro a b hab
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · exact eRows.injective hab
  have hcolMap_inj : Function.Injective colMap := by
    intro f g hfg
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    simpa [colMap, hi] using hfg
  have hRs_card : Rs.card = RC.1.card := by
    simpa [Rs, rowMap] using Finset.card_image_of_injective RC.1 hrowMap_inj
  have hCs_card : Cs.card = RC.2.card := by
    simpa [Cs, colMap] using Finset.card_image_of_injective RC.2 hcolMap_inj
  have hrow0 : ⌈(Fintype.card (R2 d) : ℝ) * β⌉₊ ≤ RC.1.card := by
    have h0 := hRows 0 (by simp)
    have hfilter : RC.1.filter (fun p : Fin 1 × R2 d => p.1 = 0) = RC.1 := by
      ext p
      simp [Subsingleton.elim p.1 0]
    simpa [hfilter] using h0
  have hR2card_eq : Fintype.card (R2 d) = 2 ^ (R + T) * Fintype.card (C1 d) := by
    simp [R2, C1, Fintype.card_prod, Fintype.card_fin, hqcast]
  have hden_pos : 0 < ((2 ^ (R + T) : ℕ) : ℝ) * (Fintype.card (C1 d) : ℝ) := by
    positivity
  have hβ_density :
      β ≤ (Rs.card : ℝ) / (((2 ^ (R + T) : ℕ) : ℝ) * (Fintype.card (C1 d) : ℝ)) := by
    have hceil_real : (⌈(Fintype.card (R2 d) : ℝ) * β⌉₊ : ℝ) ≤ (RC.1.card : ℝ) := by
      exact_mod_cast hrow0
    have hdenβ :
        (((2 ^ (R + T) : ℕ) : ℝ) * (Fintype.card (C1 d) : ℝ)) * β ≤
          (RC.1.card : ℝ) := by
      calc
        (((2 ^ (R + T) : ℕ) : ℝ) * (Fintype.card (C1 d) : ℝ)) * β
            = (Fintype.card (R2 d) : ℝ) * β := by
              rw [hR2card_eq]
              norm_num
        _ ≤ (⌈(Fintype.card (R2 d) : ℝ) * β⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (RC.1.card : ℝ) := hceil_real
    rw [hRs_card]
    have hdiv :=
      div_le_div_of_nonneg_right hdenβ (le_of_lt hden_pos)
    have hβeq : β =
        ((((2 ^ (R + T) : ℕ) : ℝ) * (Fintype.card (C1 d) : ℝ)) * β) /
          (((2 ^ (R + T) : ℕ) : ℝ) * (Fintype.card (C1 d) : ℝ)) := by
      field_simp [ne_of_gt hden_pos]
    rw [hβeq]
    exact hdiv
  have hxloc_density :
      xloc ≤ (Rs.card : ℝ) /
        (((2 ^ (R + T) : ℕ) : ℝ) * (Fintype.card (C1 d) : ℝ)) :=
    le_trans (by simpa [xloc] using hxβ) hβ_density
  obtain ⟨J, hJlower, hJrow⟩ :=
    block_balancing (X := C1 d) (q := 2 ^ (R + T)) (R := Rs)
      (x := xloc) hxloc_pos hxloc_lt_one hxloc_density
  have hneed_le_J : 2 ^ R'e * M2_hard_seed_copies d ≤ J.card := by
    have hdenom_pos : 0 < 1 - xloc := by linarith
    have hceil_mono :
        ⌈(Params.q2 d : ℝ) * (β - xloc) / (1 - xloc)⌉₊ ≤
          ⌈((2 ^ (R + T) : ℕ) : ℝ) *
            ((Rs.card : ℝ) /
              (((2 ^ (R + T) : ℕ) : ℝ) * (Fintype.card (C1 d) : ℝ)) - xloc) /
              (1 - xloc)⌉₊ := by
      apply Nat.ceil_le_ceil
      rw [← hqcast]
      have hsub :
          β - xloc ≤
            (Rs.card : ℝ) /
              (((2 ^ (R + T) : ℕ) : ℝ) * (Fintype.card (C1 d) : ℝ)) - xloc := by
        linarith
      have hdiv :
          (β - xloc) / (1 - xloc) ≤
            ((Rs.card : ℝ) /
              (((2 ^ (R + T) : ℕ) : ℝ) * (Fintype.card (C1 d) : ℝ)) - xloc) /
              (1 - xloc) :=
        div_le_div_of_nonneg_right hsub (le_of_lt hdenom_pos)
      have hq_nonneg : 0 ≤ ((2 ^ (R + T) : ℕ) : ℝ) := by positivity
      calc
        ((2 ^ (R + T) : ℕ) : ℝ) * (β - xloc) / (1 - xloc)
            = ((2 ^ (R + T) : ℕ) : ℝ) * ((β - xloc) / (1 - xloc)) := by ring
        _ ≤ ((2 ^ (R + T) : ℕ) : ℝ) *
            (((Rs.card : ℝ) /
              (((2 ^ (R + T) : ℕ) : ℝ) * (Fintype.card (C1 d) : ℝ)) - xloc) /
              (1 - xloc)) := mul_le_mul_of_nonneg_left hdiv hq_nonneg
        _ = ((2 ^ (R + T) : ℕ) : ℝ) *
            ((Rs.card : ℝ) /
              (((2 ^ (R + T) : ℕ) : ℝ) * (Fintype.card (C1 d) : ℝ)) - xloc) /
              (1 - xloc) := by ring
    exact le_trans
      (le_trans (by simpa [M2_robust_balance_gate, xloc] using hbalance) hceil_mono)
      hJlower
  obtain ⟨Qs, hQsub, hQcard⟩ :=
    Finset.exists_subset_card_eq (s := J) hneed_le_J
  have hRs : ∃ Qs : Finset (Fin (2 ^ (R + T))),
      Qs.card = 2 ^ R'e * M2_hard_seed_copies d ∧
        IsEquipartitionedGE Rs Qs
          ⌈(2 : ℝ) ^ (R'e : ℕ) *
            M2_hard_seed_rowDensity d * (Fintype.card (C1 d) : ℝ)⌉₊ := by
    refine ⟨Qs, hQcard, ?_⟩
    have hrowQ := IsEquipartitionedGE.mono_Q hJrow hQsub
    simpa [xloc, mul_assoc, mul_left_comm, mul_comm] using hrowQ
  have hCs : Params.h2 d * (2 : ℝ) ^ (-((0 : ℕ) : ℝ)) * (L2 d : ℝ) ≤
      (Cs.card : ℝ) := by
    norm_num
    have hcols_real :
        (⌈((Fintype.card (C2 d) : ℝ) ^ 1) * Params.h2 d⌉₊ : ℝ) ≤
          (Cs.card : ℝ) := by
      rw [hCs_card]
      exact_mod_cast hCols
    calc
      Params.h2 d * (L2 d : ℝ)
          = ((Fintype.card (C2 d) : ℝ) ^ 1) * Params.h2 d := by
            simp [C2, Fintype.card_fin, mul_comm]
      _ ≤ (⌈((Fintype.card (C2 d) : ℝ) ^ 1) * Params.h2 d⌉₊ : ℝ) :=
        Nat.le_ceil _
      _ ≤ (Cs.card : ℝ) := hcols_real
  have hmain : D (M1T d) + (R'e + T) ≤
      D (subgame (relaxedInterlace (M1T d) S') Rs Cs) :=
    localized_extension (X := C1 d) (Y := R1 d) (f := M1T d)
      (b := (Params.b1 d : ℝ)) (ε := ε) hb hεnonneg T R hTb
      (S := S') hS (M2_hard_seed_copies d)
      (xseed := M2_hard_seed_rowDensity d) (h := Params.h2 d)
      (hseed := M2_hard_seed_columnDensity d)
      hx1 hxseed_le_one hh0 hh1 hs0 hs1 (by simpa [T] using hp1)
      (by simpa [T] using hp2) hres hseedbd (by simpa [T, ε] using hseed_bridge)
      0 R'e (by omega) hR'eR Rs Cs hRs hCs
  have hsub_le : D (subgame (relaxedInterlace (M1T d) S') Rs Cs) ≤
      D (subgame (interlaceFun (M2 d) 1) RC.1 RC.2) := by
    let preR : {x // x ∈ Rs} → {a // a ∈ RC.1} :=
      fun x =>
        let w := Classical.choose (Finset.mem_image.mp x.2)
        ⟨w, (Classical.choose_spec (Finset.mem_image.mp x.2)).1⟩
    let preC : {y // y ∈ Cs} → {c // c ∈ RC.2} :=
      fun y =>
        let w := Classical.choose (Finset.mem_image.mp y.2)
        ⟨w, (Classical.choose_spec (Finset.mem_image.mp y.2)).1⟩
    have hM2rel :
        (fun a b => relaxedInterlace (M1T d) S' (eRows a) b) = M2 d := by
      funext a b
      simp [relaxedInterlace, S', M2, M1T, eRows]
    have heq :
        subgame (relaxedInterlace (M1T d) S') Rs Cs =
          (fun x y => subgame (interlaceFun (M2 d) 1) RC.1 RC.2
            (preR x) (preC y)) := by
      funext x y
      have hx : rowMap (preR x).1 = x.1 := by
        dsimp [preR]
        exact (Classical.choose_spec (Finset.mem_image.mp x.2)).2
      have hy : colMap (preC y).1 = y.1 := by
        dsimp [preC]
        exact (Classical.choose_spec (Finset.mem_image.mp y.2)).2
      have hfin : (preR x).1.1 = 0 := Subsingleton.elim _ _
      show relaxedInterlace (M1T d) S' x.1 y.1 =
        M2 d (preR x).1.2 ((preC y).1 (preR x).1.1)
      rw [hfin]
      change relaxedInterlace (M1T d) S' x.1 y.1 =
        M2 d (preR x).1.2 (colMap (preC y).1)
      rw [hy, ← hM2rel]
      exact congrArg (fun z => relaxedInterlace (M1T d) S' z y.1) hx.symm
    rw [heq]
    exact D_mapNodes_le (subgame (interlaceFun (M2 d) 1) RC.1 RC.2) preR preC
  exact le_trans hmain hsub_le

-- CLAIM-BEGIN lem:M2-robust
theorem M2_robust (d : ℕ) (hpow : IsPow2 d)
    (hlog256 : 256 ≤ Nat.log 2 d)
    (hlarge : Checklist d)
    (hm0_le : (Classical.choose
        (hard_seed.{0} Params.jSurplus (by norm_num [Params.jSurplus])
          Params.delta (by norm_num [Params.delta])
          (by norm_num [Params.delta])) : ℕ) ≤ Nat.log 2 (Params.t2 d))
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d))
    (hp1 : 2 ^ M2_T d ≤ 2 * M2_hard_seed_copies d)
    (hp2 : M2_hard_seed_copies d ≤ 2 ^ M2_T d)
    (hxseed_le_one : M2_hard_seed_rowDensity d ≤ 1)
    (hrow_threshold :
      ⌈(2 : ℝ) ^ (Nat.log 2 (Params.r2 d) : ℕ) *
        M2_hard_seed_rowDensity d * (Fintype.card (C1 d) : ℝ)⌉₊
          ≤ Fintype.card (C1 d))
    (hseed_bridge : M2_hard_seed_columnDensity d ≤
      Params.h2 d *
        (2 : ℝ) ^ (-((M2_T d + D (M1T d) : ℕ) : ℝ)) /
          (1 + epsQT (Params.q2 d) (Params.t2 d)))
    (hy_le_one : M1_stage2_terminal_density d ≤ 1)
    (hrowTerm : 9 * Params.t1 d ≤
      16 * ⌈(Fintype.card (R1 d) : ℝ) * M1_stage2_terminal_density d⌉₊)
    (hcolTerm : (2 : ℝ) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : ℤ))
        * (Fintype.card (C1 d) : ℝ) ≤
      (⌈(Fintype.card (C1 d) : ℝ) *
        ((2 : ℝ) ^ (-(Params.b1 d : ℤ)))⌉₊ : ℝ))
    (hresidual_density : ∀ c ≤ M2_T d + D (M1T d),
      1 / 2 + Params.delta ≤
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c ∧
        yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c ≤ 1)
    (hRlog_ge2 : 2 ≤ Nat.log 2 (Params.r2 d))
    (hx_top : (2 : ℝ) ^ Nat.log 2 (Params.r2 d) *
        M2_hard_seed_rowDensity d ≤ 1 / 2 + Params.delta)
    (hx_mid : (2 : ℝ) ^ (Nat.log 2 (Params.r2 d) - 1) *
        M2_hard_seed_rowDensity d ≤ 1 / 4 + Params.delta / 2)
    (hx_low : (2 : ℝ) ^ (Nat.log 2 (Params.r2 d) - 2) *
        M2_hard_seed_rowDensity d ≤ 1 / 8 + Params.delta / 4)
    (hbalance_top :
      M2_robust_balance_gate d (Nat.log 2 (Params.r2 d)) (1 / 2 + Params.delta))
    (hbalance_mid :
      M2_robust_balance_gate d (Nat.log 2 (Params.r2 d) - 1)
        (1 / 4 + Params.delta / 2))
    (hbalance_low :
      M2_robust_balance_gate d (Nat.log 2 (Params.r2 d) - 2)
        (1 / 8 + Params.delta / 4)) :
    IsRobust (fun (c : C2 d) (r : R2 d) => M2 d r c) Params.delta (Params.b2 d) := by
  classical
  let MT : C2 d → R2 d → Bool := fun c r => M2 d r c
  change IsRobust MT Params.delta (Params.b2 d)
  let T : ℕ := M2_T d
  let R : ℕ := Nat.log 2 (Params.r2 d)
  have hlog64 : 64 ≤ Nat.log 2 d := by omega
  have hqcast : 2 ^ (R + T) = Params.q2 d := by
    calc
      2 ^ (R + T) = 2 ^ R * 2 ^ T := by rw [pow_add]
      _ = Params.r2 d * Params.t2 d := by
        dsimp [R, T]
        rw [← hr2pow, ← t2_eq_two_pow_M2_T d]
      _ = Params.q2 d := hlarge.q2_eq.symm
  have hQeq : R + T = Nat.log 2 (Params.q2 d) := by
    rw [← hqcast, log_two_pow]
  have hM1comp : D (M1 d) = Params.a d + 1 := M1_complexity d hpow hlog64
  have hcomp := M2_complexity d hpow hlog256 hlarge hm0_le hr2pow hp1 hp2
    hxseed_le_one hrow_threshold hseed_bridge hy_le_one hrowTerm hcolTerm
    hresidual_density
  have htr : D MT = D (M2 d) := by
    simpa [MT] using comp_transpose (M2 d)
  have hswap : D (M1T d) = D (M1 d) := by
    simpa [M1T] using comp_transpose (M1 d)
  have hh0 : 0 < Params.h2 d := Params.h2_pos
  have hh1 : Params.h2 d ≤ 1 := by
    unfold Params.h2
    rw [two_zpow_neg_nat_eq_rpow_neg_nat_stage2 (Params.b2 d)]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
    exact neg_nonpos.mpr (Nat.cast_nonneg _)
  have hC1card_pos : 0 < Fintype.card (C1 d) := by
    simpa [C1, Fintype.card_fin] using L1_pos d hlarge.t1_le_q1_add_five
  have hR2card : 1 ≤ Fintype.card (R2 d) := by
    exact Nat.succ_le_of_lt (by
      simpa [R2, C1, Fintype.card_prod, Fintype.card_fin] using
        Nat.mul_pos (Params.q2_pos d) hC1card_pos)
  have hC2card : 1 ≤ Fintype.card (C2 d) := by
    simpa [C2, Fintype.card_fin] using
      L2_pos d hlarge.t2_le_q2 hlarge.one_le_q1
  have htop_orig : D (M1T d) + (R + T) ≤
      Dfamily (interlaceFun (M2 d) 1)
        (bracketGE (R2 d) (C2 d) 1 (1 / 2 + Params.delta) (Params.h2 d)) := by
    simpa [R, T] using
      M2_family_lower_from_localized d hpow hlog256 hlarge hm0_le hr2pow hp1 hp2
        hxseed_le_one hseed_bridge hy_le_one hrowTerm hcolTerm hresidual_density
        (β := 1 / 2 + Params.delta) (R'e := Nat.log 2 (Params.r2 d))
        (le_refl _) (by norm_num [Params.delta]) (by norm_num [Params.delta])
        hx_top hbalance_top
  have hmid_orig : D (M1T d) + ((R - 1) + T) ≤
      Dfamily (interlaceFun (M2 d) 1)
        (bracketGE (R2 d) (C2 d) 1 (1 / 4 + Params.delta / 2) (Params.h2 d)) := by
    simpa [R, T] using
      M2_family_lower_from_localized d hpow hlog256 hlarge hm0_le hr2pow hp1 hp2
        hxseed_le_one hseed_bridge hy_le_one hrowTerm hcolTerm hresidual_density
        (β := 1 / 4 + Params.delta / 2) (R'e := Nat.log 2 (Params.r2 d) - 1)
        (by omega) (by norm_num [Params.delta]) (by norm_num [Params.delta])
        hx_mid hbalance_mid
  have hlow_orig : D (M1T d) + ((R - 2) + T) ≤
      Dfamily (interlaceFun (M2 d) 1)
        (bracketGE (R2 d) (C2 d) 1 (1 / 8 + Params.delta / 4) (Params.h2 d)) := by
    simpa [R, T] using
      M2_family_lower_from_localized d hpow hlog256 hlarge hm0_le hr2pow hp1 hp2
        hxseed_le_one hseed_bridge hy_le_one hrowTerm hcolTerm hresidual_density
        (β := 1 / 8 + Params.delta / 4) (R'e := Nat.log 2 (Params.r2 d) - 2)
        (by omega) (by norm_num [Params.delta]) (by norm_num [Params.delta])
        hx_low hbalance_low
  have htrans_top :=
    Dfamily_one_transpose (M2 d)
      (x := 1 / 2 + Params.delta) (y := Params.h2 d)
      (by norm_num [Params.delta]) (by norm_num [Params.delta])
      hh0 hh1 hR2card hC2card
  have htrans_mid :=
    Dfamily_one_transpose (M2 d)
      (x := 1 / 4 + Params.delta / 2) (y := Params.h2 d)
      (by norm_num [Params.delta]) (by norm_num [Params.delta])
      hh0 hh1 hR2card hC2card
  have htrans_low :=
    Dfamily_one_transpose (M2 d)
      (x := 1 / 8 + Params.delta / 4) (y := Params.h2 d)
      (by norm_num [Params.delta]) (by norm_num [Params.delta])
      hh0 hh1 hR2card hC2card
  unfold IsRobust
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [htr, hcomp, hM1comp]
    omega
  · have htop_nat : D MT ≤
        Dfamily (interlaceFun (M2 d) 1)
          (bracketGE (R2 d) (C2 d) 1 (1 / 2 + Params.delta) (Params.h2 d)) := by
      rw [htr, hcomp, ← hQeq, ← hswap]
      exact htop_orig
    have htop_trans : D MT ≤
        Dfamily (interlaceFun MT 1)
          (bracketGE (C2 d) (R2 d) 1 ((2 : ℝ) ^ (-(Params.b2 d : ℝ)))
            (1 / 2 + Params.delta)) := by
      rw [show (2 : ℝ) ^ (-(Params.b2 d : ℝ)) = Params.h2 d by
        unfold Params.h2
        rw [two_zpow_neg_nat_eq_rpow_neg_nat_stage2 (Params.b2 d)]]
      have htarget_eq :
          Dfamily (interlaceFun MT 1)
              (bracketGE (C2 d) (R2 d) 1 (Params.h2 d) (1 / 2 + Params.delta))
            =
          Dfamily (interlaceFun (M2 d) 1)
              (bracketGE (R2 d) (C2 d) 1 (1 / 2 + Params.delta) (Params.h2 d)) := by
        simpa [MT] using htrans_top
      rw [htarget_eq]
      exact htop_nat
    exact htop_trans
  · have hlow_int : ((D MT : ℤ) - 2) ≤
        (Dfamily (interlaceFun (M2 d) 1)
          (bracketGE (R2 d) (C2 d) 1 (1 / 8 + Params.delta / 4)
            (Params.h2 d)) : ℤ) := by
      rw [htr, hcomp]
      calc
        (((D (M1 d) + Nat.log 2 (Params.q2 d) : ℕ) : ℤ) - 2)
            = ((D (M1T d) + ((R - 2) + T) : ℕ) : ℤ) := by
              rw [← hswap, ← hQeq]
              omega
        _ ≤ (Dfamily (interlaceFun (M2 d) 1)
          (bracketGE (R2 d) (C2 d) 1 (1 / 8 + Params.delta / 4)
            (Params.h2 d)) : ℤ) := by
              exact_mod_cast hlow_orig
    rw [show (2 : ℝ) ^ (-(Params.b2 d : ℝ)) = Params.h2 d by
      unfold Params.h2
      rw [two_zpow_neg_nat_eq_rpow_neg_nat_stage2 (Params.b2 d)]]
    change ((D MT : ℤ) - 2) ≤
      (Dfamily (interlaceFun MT 1)
        (bracketGE (C2 d) (R2 d) 1 (Params.h2 d)
          (1 / 8 + Params.delta / 4)) : ℤ)
    have htarget_eq :
        Dfamily (interlaceFun MT 1)
            (bracketGE (C2 d) (R2 d) 1 (Params.h2 d)
              (1 / 8 + Params.delta / 4))
          =
        Dfamily (interlaceFun (M2 d) 1)
            (bracketGE (R2 d) (C2 d) 1 (1 / 8 + Params.delta / 4)
              (Params.h2 d)) := by
      simpa [MT] using htrans_low
    rw [htarget_eq]
    exact hlow_int
  · have hmid_int : ((D MT : ℤ) - 1) ≤
        (Dfamily (interlaceFun (M2 d) 1)
          (bracketGE (R2 d) (C2 d) 1 (1 / 4 + Params.delta / 2)
            (Params.h2 d)) : ℤ) := by
      rw [htr, hcomp]
      calc
        (((D (M1 d) + Nat.log 2 (Params.q2 d) : ℕ) : ℤ) - 1)
            = ((D (M1T d) + ((R - 1) + T) : ℕ) : ℤ) := by
              rw [← hswap, ← hQeq]
              omega
        _ ≤ (Dfamily (interlaceFun (M2 d) 1)
          (bracketGE (R2 d) (C2 d) 1 (1 / 4 + Params.delta / 2)
            (Params.h2 d)) : ℤ) := by
              exact_mod_cast hmid_orig
    rw [show (2 : ℝ) ^ (-(Params.b2 d : ℝ)) = Params.h2 d by
      unfold Params.h2
      rw [two_zpow_neg_nat_eq_rpow_neg_nat_stage2 (Params.b2 d)]]
    change ((D MT : ℤ) - 1) ≤
      (Dfamily (interlaceFun MT 1)
        (bracketGE (C2 d) (R2 d) 1 (Params.h2 d)
          (1 / 4 + Params.delta / 2)) : ℤ)
    have htarget_eq :
        Dfamily (interlaceFun MT 1)
            (bracketGE (C2 d) (R2 d) 1 (Params.h2 d)
              (1 / 4 + Params.delta / 2))
          =
        Dfamily (interlaceFun (M2 d) 1)
            (bracketGE (R2 d) (C2 d) 1 (1 / 4 + Params.delta / 2)
              (Params.h2 d)) := by
      simpa [MT] using htrans_mid
    rw [htarget_eq]
    exact hmid_int
-- CLAIM-END lem:M2-robust
-- CLAIM-BEGIN aux:m2-dense-separation-core
/-- Dense-row Stage-2 separation core.  This is the part of paper
`cor:M2SeparationTransposeDenseRows` that is presently certified by the live
`relaxed_separation` interface: after swapping a protocol for the transposed
dense-row subgame back to the Stage-2 relaxed-interlace orientation, any
budget-tight protocol has the first `log q₂` bits isolating the dimension block
and satisfies the no-waste dominant-block conclusion on the retained dense
column set.  The promoted `BranchAt` packaging and the final per-dimension
survivor relabelling are intentionally not assumed here. -/
theorem M2_separation_transpose_dense_rows (d : ℕ) (hpow : IsPow2 d)
    (hlog256 : 256 ≤ Nat.log 2 d)
    (hlarge : Checklist d)
    (hm0_le : (Classical.choose
        (hard_seed.{0} Params.jSurplus (by norm_num [Params.jSurplus])
          Params.delta (by norm_num [Params.delta])
          (by norm_num [Params.delta])) : ℕ) ≤ Nat.log 2 (Params.t2 d))
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d))
    (hp1 : 2 ^ M2_T d ≤ 2 * M2_hard_seed_copies d)
    (hp2 : M2_hard_seed_copies d ≤ 2 ^ M2_T d)
    (hxseed_le_one : M2_hard_seed_rowDensity d ≤ 1)
    (hrow_threshold :
      ⌈(2 : ℝ) ^ (Nat.log 2 (Params.r2 d) : ℕ) *
        M2_hard_seed_rowDensity d * (Fintype.card (C1 d) : ℝ)⌉₊
          ≤ Fintype.card (C1 d))
    (hseed_bridge : M2_hard_seed_columnDensity d ≤
      Params.h2 d *
        (2 : ℝ) ^ (-((M2_T d + D (M1T d) : ℕ) : ℝ)) /
          (1 + epsQT (Params.q2 d) (Params.t2 d)))
    (hy_le_one : M1_stage2_terminal_density d ≤ 1)
    (hrowTerm : 9 * Params.t1 d ≤
      16 * ⌈(Fintype.card (R1 d) : ℝ) * M1_stage2_terminal_density d⌉₊)
    (hcolTerm : (2 : ℝ) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : ℤ))
        * (Fintype.card (C1 d) : ℝ) ≤
      (⌈(Fintype.card (C1 d) : ℝ) *
        ((2 : ℝ) ^ (-(Params.b1 d : ℤ)))⌉₊ : ℝ))
    (hresidual_density : ∀ c ≤ M2_T d + D (M1T d),
      1 / 2 + Params.delta ≤
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c ∧
        yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c ≤ 1)
    (hqcast : 2 ^ (Nat.log 2 (Params.r2 d) + M2_T d) = Params.q2 d)
    (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hσ_dense : 1 - 8 * Params.h2 d ≤ σ)
    (hres_dense : IsColumnLossResilient (M1T d) (Params.b1 d : ℝ)
      (epsQT (Params.q2 d) (Params.t2 d))
      (Nat.log 2 (Params.q2 d)) (M2_T d) σ)
    (hxseed_le_inv_r : M2_hard_seed_rowDensity d ≤
      (2 : ℝ) ^ (-(Nat.log 2 (Params.r2 d) : ℝ)))
    (hseed_bridge_dense : M2_hard_seed_columnDensity d ≤
      σ *
        (2 : ℝ) ^ (-((M2_T d + D (M1T d) : ℕ) : ℝ)) /
          (1 + epsQT (Params.q2 d) (Params.t2 d)))
    (hdelta_sep : Params.delta ≤ 1 / Real.sqrt 2 - 1 / 2)
    (hT1 : 1 ≤ M2_T d)
    (hgap :
      2 ^ (Nat.log 2 (Params.r2 d) + M2_T d) *
        ⌈(2 : ℝ) ^ (1 - (Params.b1 d : ℝ)) *
          (Fintype.card (C1 d) : ℝ)⌉₊ < Fintype.card (C1 d))
    (Sdense : Finset (C2 d))
    (hSdense : σ * (L2 d : ℝ) ≤ (Sdense.card : ℝ))
    (P : Protocol
      {a // a ∈
        (Finset.univ :
          Finset (Fin (2 ^ (Nat.log 2 (Params.r2 d) + M2_T d)) × C1 d))}
      {c // c ∈ Sdense} Bool)
    (hP : P.Computes (subgame
      (relaxedInterlace (M1T d)
        (fun j γ => S2fam d j (Fin.cast hqcast γ)))
      (Finset.univ :
        Finset (Fin (2 ^ (Nat.log 2 (Params.r2 d) + M2_T d)) × C1 d))
      Sdense))
    (hcost : P.cost ≤ D (M2 d)) :
    Protocol.FirstKRowBitsOn
        (Finset.univ :
          Finset {a // a ∈
            (Finset.univ :
              Finset (Fin (2 ^ (Nat.log 2 (Params.r2 d) + M2_T d)) × C1 d))})
        (Finset.univ : Finset {c // c ∈ Sdense})
        (Nat.log 2 (Params.r2 d) + M2_T d) P
    ∧ NoWasteConclusion
        (Finset.univ : Finset (Fin (2 ^ (Nat.log 2 (Params.r2 d) + M2_T d))))
        (Finset.univ :
          Finset (Fin (2 ^ (Nat.log 2 (Params.r2 d) + M2_T d)) × C1 d))
        (Protocol.prefixLabelFinQ
          (Finset.univ :
            Finset (Fin (2 ^ (Nat.log 2 (Params.r2 d) + M2_T d)) × C1 d)) P)
        (Fintype.card (C1 d))
        ⌈(2 : ℝ) ^ (1 - (Params.b1 d : ℝ)) *
          (Fintype.card (C1 d) : ℝ)⌉₊ := by
-- CLAIM-END aux:m2-dense-separation-core
  classical
  let T : ℕ := M2_T d
  let R : ℕ := Nat.log 2 (Params.r2 d)
  let ε : ℝ := epsQT (Params.q2 d) (Params.t2 d)
  let S : Fin (L2 d) → Fin (2 ^ (R + T)) → R1 d :=
    fun j γ => S2fam d j (Fin.cast (by simpa [R, T] using hqcast) γ)
  have hQeq : R + T = Nat.log 2 (Params.q2 d) := by
    rw [← hqcast]
    simp [R, T]
  have hlog64 : 64 ≤ Nat.log 2 d := by omega
  have hm_le_b1 : (Nat.log 2 (Params.t2 d) : ℝ) ≤ (Params.b1 d : ℝ) := by
    have hpowle : 2 ^ Nat.log 2 (Params.t2 d) ≤ 2 ^ Params.b1 d := by
      rw [← t2_eq_two_pow_log d]
      exact hlarge.t2_le_pow_b1
    exact_mod_cast (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpowle
  have hb : (1 : ℝ) ≤ (Params.b1 d : ℝ) := by
    have hb1nat : 1 ≤ Params.b1 d := by
      unfold Params.b1
      omega
    exact_mod_cast hb1nat
  have hlogt_eq_T : Nat.log 2 (Params.t2 d) = T := by
    dsimp [T]
    rw [t2_eq_two_pow_M2_T, log_two_pow]
  have hTb : (T : ℝ) ≤ (Params.b1 d : ℝ) := by
    simpa [hlogt_eq_T] using hm_le_b1
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact epsQT_pos (Params.q2_pos d) (Params.t2_pos d)
  have hεnonneg : 0 ≤ ε := le_of_lt hεpos
  have hSbase : IsBalancedFamily (Params.t2 d) (S2fam d) ε := by
    dsimp [ε]
    exact S2fam_balanced d hlarge.t2_le_q2 hlarge.one_le_q1
  have hcast_inj :
      Function.Injective
        (fun γ : Fin (2 ^ (R + T)) =>
          Fin.cast (by simpa [R, T] using hqcast) γ) := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg (fun z : Fin (Params.q2 d) => z.val) hab
    simpa using hv
  have hSproj :=
    hSbase.projection
      (fun γ : Fin (2 ^ (R + T)) =>
        Fin.cast (by simpa [R, T] using hqcast) γ) hcast_inj
  have hS : IsBalancedFamily (2 ^ T) S ε := by
    simpa [S, T, t2_eq_two_pow_M2_T d] using hSproj
  have hseed0 := M2_hard_seed d hpow hlog256 hm0_le hm_le_b1
  have hseedbd : D (M1T d) + T ≤
      Dfamily (interlaceFun (M1T d) (M2_hard_seed_copies d))
        (bracketGE (C1 d) (R1 d) (M2_hard_seed_copies d)
          (M2_hard_seed_rowDensity d) (M2_hard_seed_columnDensity d)) := by
    simpa [hlogt_eq_T] using hseed0
  have hx1 : (2 : ℝ) ^ (-(Params.b1 d : ℝ)) ≤ M2_hard_seed_rowDensity d := by
    unfold M2_hard_seed_rowDensity
    have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 (Params.t2 d) : ℕ) :=
      one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hnonneg : 0 ≤ (2 : ℝ) ^ (-(Params.b1 d : ℝ)) := by positivity
    calc
      (2 : ℝ) ^ (-(Params.b1 d : ℝ))
          = 1 * (2 : ℝ) ^ (-(Params.b1 d : ℝ)) := by ring
      _ ≤ (2 : ℝ) ^ (Nat.log 2 (Params.t2 d) : ℕ) *
          (2 : ℝ) ^ (-(Params.b1 d : ℝ)) :=
            mul_le_mul_of_nonneg_right hpow1 hnonneg
  have hs0 : 0 < M2_hard_seed_columnDensity d := by
    unfold M2_hard_seed_columnDensity
    positivity
  have hs1 : M2_hard_seed_columnDensity d ≤ 1 := by
    unfold M2_hard_seed_columnDensity
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
    exact neg_nonpos.mpr (by positivity)
  have hD : 2 ≤ D (M1T d) := by
    have hcomp := M1T_complexity d hpow hlog64
    rw [hcomp]
    have ha : 2 ≤ Params.a d := hlarge.a_ge_two
    omega
  have hrob : IsRobust (M1T d) Params.delta (Params.b1 d) := by
    simpa [M1T] using M1_robust d hpow hlog256
  have hres : IsColumnLossResilient (M1T d) (Params.b1 d : ℝ) ε (R + T) T σ := by
    simpa [ε, T, R, hQeq] using hres_dense
  have hM2comp := M2_complexity d hpow hlog256 hlarge hm0_le hr2pow hp1 hp2
    hxseed_le_one hrow_threshold hseed_bridge hy_le_one hrowTerm hcolTerm
    hresidual_density
  have hbudget : P.cost ≤ D (M1T d) + (R + T) := by
    have hcost' := hcost
    rw [hM2comp] at hcost'
    have hswap : D (M1T d) = D (M1 d) := by
      simpa [M1T] using comp_transpose (M1 d)
    rw [hswap]
    simpa [hQeq] using hcost'
  have hband_dense :
      2 * (1 / 2 + Params.delta) ^ 2 ≤ σ / (1 + ε) := by
    dsimp [ε]
    exact hlarge.dens_sep_dense σ hσ_dense
  have hSdense' : σ * (L2 d : ℝ) ≤ (Sdense.card : ℝ) := hSdense
  simpa [S, R, T, ε] using
    relaxed_separation (f := M1T d) (δ := Params.delta)
      (b := (Params.b1 d : ℝ)) (ε := ε) hb hεnonneg T R hTb
      (S := S) hS (M2_hard_seed_copies d)
      (xseed := M2_hard_seed_rowDensity d) (h := σ)
      (hseed := M2_hard_seed_columnDensity d)
      hx1 hxseed_le_inv_r hσ0 hσ1 hs0 hs1
      (by simpa [T] using hp1) (by simpa [T] using hp2)
      hres hseedbd (by simpa [T, ε] using hseed_bridge_dense)
      hrob (by norm_num [Params.delta]) hdelta_sep hD hT1
      hband_dense (by simpa [R, T] using hgap)
      Sdense hSdense' P hP hbudget

end NPCC

namespace NPCC

open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open Workspace.Types.BoolMat
open Workspace.Types.MatComplexity

-- CLAIM-BEGIN aux:m2-numerics

/-- Public Stage-2 copy of the exact structural identity for `t2`. -/
theorem M2num_t2_eq_two_pow_M2_T (d : ℕ) :
    Params.t2 d = 2 ^ M2_T d := by
  rfl

/-- Public Stage-2 copy of the exact logarithmic identity for `t2`. -/
theorem M2num_log2_t2_eq_M2_T (d : ℕ) :
    Nat.log 2 (Params.t2 d) = M2_T d := by
  rw [M2num_t2_eq_two_pow_M2_T, log_two_pow]

/-- The `q2 = r2 * t2` checklist identity rewritten on logarithms. -/
theorem M2num_log2_q2_eq_log2_r2_add_log2_t2 (d : ℕ)
    (hlarge : Checklist d)
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d)) :
    Nat.log 2 (Params.q2 d) =
      Nat.log 2 (Params.r2 d) + Nat.log 2 (Params.t2 d) := by
  have hqpow :
      Params.q2 d =
        2 ^ (Nat.log 2 (Params.r2 d) + Nat.log 2 (Params.t2 d)) := by
    have htt : Params.t2 d = 2 ^ M2_T d := M2num_t2_eq_two_pow_M2_T d
    calc
      Params.q2 d = Params.r2 d * Params.t2 d := hlarge.q2_eq
      _ = Params.r2 d * 2 ^ M2_T d := by
            exact congrArg (fun z => Params.r2 d * z) htt
      _ = 2 ^ Nat.log 2 (Params.r2 d) * 2 ^ M2_T d := by
            exact congrArg (fun z => z * 2 ^ M2_T d) hr2pow
      _ = 2 ^ (Nat.log 2 (Params.r2 d) + M2_T d) := by
            rw [pow_add]
      _ = 2 ^ (Nat.log 2 (Params.r2 d) + Nat.log 2 (Params.t2 d)) := by
            rw [M2num_log2_t2_eq_M2_T d]
  rw [hqpow, log_two_pow]

/-- At the Stage-2 entry threshold, `t2` has at least five binary bits. -/
theorem M2num_M2_T_ge_five (d : ℕ)
    (hlog256 : 256 ≤ Nat.log 2 d) :
    5 ≤ M2_T d := by
  have hell8 : 8 ≤ Nat.log 2 (Nat.log 2 d) := by
    calc
      8 = Nat.log 2 (2 ^ 8) := by rw [log_two_pow]
      _ ≤ Nat.log 2 (Nat.log 2 d) := Nat.log_mono_right hlog256
  have ht2ge : 3 * Nat.log 2 (Nat.log 2 d) + 2 ≤ Params.t2 d :=
    Params.t2_ge hlog256
  have ht2ge26 : 26 ≤ Params.t2 d := by nlinarith
  rw [M2num_t2_eq_two_pow_M2_T d] at ht2ge26
  by_contra hnot
  have hTle : M2_T d ≤ 4 := by omega
  have hpowle : 2 ^ M2_T d ≤ 2 ^ 4 :=
    Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hTle
  norm_num at hpowle
  omega

/-- The lower copy-count side for the Stage-2 hard seed. -/
theorem M2num_hard_seed_copy_lower (d : ℕ)
    (hT5 : 5 ≤ M2_T d) :
    2 ^ M2_T d ≤ 2 * M2_hard_seed_copies d := by
  have hlogT : Nat.log 2 (Params.t2 d) = M2_T d :=
    M2num_log2_t2_eq_M2_T d
  unfold M2_hard_seed_copies
  rw [hlogT]
  have hsplit : M2_T d = 5 + (M2_T d - 5) := by omega
  rw [hsplit, pow_add]
  norm_num [Params.jSurplus]
  omega

/-- The upper copy-count side for the Stage-2 hard seed. -/
theorem M2num_hard_seed_copy_upper (d : ℕ)
    (hT5 : 5 ≤ M2_T d) :
    M2_hard_seed_copies d ≤ 2 ^ M2_T d := by
  have hlogT : Nat.log 2 (Params.t2 d) = M2_T d :=
    M2num_log2_t2_eq_M2_T d
  unfold M2_hard_seed_copies
  rw [hlogT]
  have hsplit : M2_T d = 5 + (M2_T d - 5) := by omega
  rw [hsplit, pow_add]
  norm_num [Params.jSurplus]

/-- The Stage-2 residual density is always at most one at the `h2` scale. -/
theorem M2num_yLoss_le_one (d : ℕ) (c : ℕ) :
    yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
      (Params.h2 d) c ≤ 1 := by
  apply yLoss_le_one
  · have hεnonneg : 0 ≤ epsQT (Params.q2 d) (Params.t2 d) :=
      le_of_lt (epsQT_pos (Params.q2_pos d) (Params.t2_pos d))
    have hdenpos : 0 < 1 + epsQT (Params.q2 d) (Params.t2 d) := by
      linarith
    have hh2nonneg : 0 ≤ Params.h2 d := le_of_lt Params.h2_pos
    have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (-(c : ℝ)) := by positivity
    exact div_nonneg (mul_nonneg hh2nonneg hpow_nonneg) (le_of_lt hdenpos)
  · have hh2le : Params.h2 d ≤ 1 := by
      unfold Params.h2
      rw [two_zpow_neg_nat_eq_rpow_neg_nat_stage2 (Params.b2 d)]
      exact Real.rpow_le_one_of_one_le_of_nonpos
        (by norm_num : (1 : ℝ) ≤ 2)
        (neg_nonpos.mpr (Nat.cast_nonneg _))
    have hpowle : (2 : ℝ) ^ (-(c : ℝ)) ≤ 1 := by
      calc
        (2 : ℝ) ^ (-(c : ℝ)) ≤ (2 : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le
            (by norm_num : (1 : ℝ) ≤ 2)
            (neg_nonpos.mpr (Nat.cast_nonneg _))
        _ = 1 := by norm_num
    have hnum : Params.h2 d * (2 : ℝ) ^ (-(c : ℝ)) ≤ 1 := by
      calc
        Params.h2 d * (2 : ℝ) ^ (-(c : ℝ)) ≤ 1 * 1 := by
          exact mul_le_mul hh2le hpowle (by positivity) (by positivity)
        _ = 1 := by norm_num
    have hεnonneg : 0 ≤ epsQT (Params.q2 d) (Params.t2 d) :=
      le_of_lt (epsQT_pos (Params.q2_pos d) (Params.t2_pos d))
    have hdenpos : 0 < 1 + epsQT (Params.q2 d) (Params.t2 d) := by
      linarith
    rw [div_le_iff₀ hdenpos]
    nlinarith

/-- A `3/5` residual window supplies the live `1/2 + delta` window. -/
theorem M2num_residual_density_of_three_fifths (d : ℕ)
    (hy :
      ∀ c ≤ M2_T d + D (M1T d),
        (3 : ℝ) / 5 ≤
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c) :
    ∀ c ≤ M2_T d + D (M1T d),
      1 / 2 + Params.delta ≤
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c ∧
        yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c ≤ 1 := by
  intro c hc
  constructor
  · have hdelta : (1 / 2 : ℝ) + Params.delta = (3 : ℝ) / 5 := by
      norm_num [Params.delta]
    rw [hdelta]
    exact hy c hc
  · exact M2num_yLoss_le_one d c

/-- Exponent gate saying the raw hard-seed density is no larger than `h2'`. -/
def M2_hard_seed_to_h2prime_exp (d : ℕ) : Prop :=
  (Params.b2' d : ℝ) ≤
    (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (M2_T d : ℝ))

/-- Exponent gate saying `h2'` fits inside the Stage-2 bridge budget. -/
def M2_h2prime_bridge_exp (d : ℕ) : Prop :=
  Params.b2 d + (M2_T d + D (M1T d)) + 1 ≤ Params.b2' d

/-- The raw hard-seed density is below `h2'` under the corresponding exponent
gate. This is the paper's monotonicity upgrade, stated at the density level. -/
theorem M2num_hard_seed_columnDensity_le_h2prime (d : ℕ)
    (hexp : M2_hard_seed_to_h2prime_exp d) :
    M2_hard_seed_columnDensity d ≤ Params.h2' d := by
  unfold M2_hard_seed_to_h2prime_exp at hexp
  unfold M2_hard_seed_columnDensity Params.h2'
  rw [M2num_log2_t2_eq_M2_T d]
  rw [two_zpow_neg_nat_eq_rpow_neg_nat_stage2 (Params.b2' d)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  linarith

/-- The auxiliary density `h2'` is below the live bridge budget once the
integer exponent comparison is supplied. -/
theorem M2num_h2prime_le_bridge (d : ℕ)
    (hexp : M2_h2prime_bridge_exp d) :
    Params.h2' d ≤
      Params.h2 d *
        (2 : ℝ) ^ (-((M2_T d + D (M1T d) : ℕ) : ℝ)) /
          (1 + epsQT (Params.q2 d) (Params.t2 d)) := by
  unfold M2_h2prime_bridge_exp at hexp
  let C : ℕ := M2_T d + D (M1T d)
  let A : ℕ := Params.b2 d + C + 1
  let ε : ℝ := epsQT (Params.q2 d) (Params.t2 d)
  have hεle : ε ≤ 1 := by
    dsimp [ε]
    exact le_trans (epsQT_le_half (Params.q2_pos d) (Params.t2_pos d))
      (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact epsQT_pos (Params.q2_pos d) (Params.t2_pos d)
  have hdenpos : 0 < 1 + ε := by linarith
  have hnum_nonneg :
      0 ≤ Params.h2 d * (2 : ℝ) ^ (-(C : ℝ)) := by
    exact mul_nonneg (le_of_lt Params.h2_pos) (by positivity)
  have hhalf_le :
      Params.h2 d * (2 : ℝ) ^ (-(C : ℝ)) / 2 ≤
        Params.h2 d * (2 : ℝ) ^ (-(C : ℝ)) / (1 + ε) := by
    exact div_le_div_of_nonneg_left hnum_nonneg hdenpos (by linarith)
  have hhalf_eq :
      Params.h2 d * (2 : ℝ) ^ (-(C : ℝ)) / 2 =
        (2 : ℝ) ^ (-(A : ℝ)) := by
    have htwo_pos : (0 : ℝ) < 2 := by norm_num
    have hcastA : (A : ℝ) = (Params.b2 d : ℝ) + (C : ℝ) + 1 := by
      dsimp [A]
      norm_num
    unfold Params.h2
    rw [two_zpow_neg_nat_eq_rpow_neg_nat_stage2 (Params.b2 d)]
    calc
      (2 : ℝ) ^ (-(Params.b2 d : ℝ)) * (2 : ℝ) ^ (-(C : ℝ)) / 2
          = (2 : ℝ) ^ (-(Params.b2 d : ℝ)) *
              (2 : ℝ) ^ (-(C : ℝ)) * (2 : ℝ) ^ (-1 : ℝ) := by
                rw [Real.rpow_neg_one]
                ring_nf
      _ = (2 : ℝ) ^
            (-(Params.b2 d : ℝ) + -(C : ℝ) + (-1 : ℝ)) := by
              rw [← Real.rpow_add htwo_pos, ← Real.rpow_add htwo_pos]
      _ = (2 : ℝ) ^ (-(A : ℝ)) := by
              rw [hcastA]
              congr 1
              ring
  have hprime_le_half :
      Params.h2' d ≤ Params.h2 d * (2 : ℝ) ^ (-(C : ℝ)) / 2 := by
    rw [hhalf_eq]
    unfold Params.h2'
    rw [two_zpow_neg_nat_eq_rpow_neg_nat_stage2 (Params.b2' d)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    have hA_le : A ≤ Params.b2' d := by
      dsimp [A, C]
      exact hexp
    exact neg_le_neg (by exact_mod_cast hA_le)
  dsimp [C, ε] at hhalf_le hprime_le_half
  exact le_trans hprime_le_half hhalf_le

/-- The h2-prime route supplies the raw bridge expected by the live
`M2_complexity` theorem. -/
theorem M2num_hbridge_via_h2prime (d : ℕ)
    (hraw : M2_hard_seed_to_h2prime_exp d)
    (hprime : M2_h2prime_bridge_exp d) :
    M2_hard_seed_columnDensity d ≤
      Params.h2 d *
        (2 : ℝ) ^ (-((M2_T d + D (M1T d) : ℕ) : ℝ)) /
          (1 + epsQT (Params.q2 d) (Params.t2 d)) := by
  exact le_trans (M2num_hard_seed_columnDensity_le_h2prime d hraw)
    (M2num_h2prime_le_bridge d hprime)

/-- The hard-seed row density is at most one from the checklist copy-budget
field `t2 <= 2^b1`. -/
theorem M2num_hard_seed_rowDensity_le_one (d : ℕ)
    (hlarge : Checklist d) :
    M2_hard_seed_rowDensity d ≤ 1 := by
  unfold M2_hard_seed_rowDensity
  have hpowle_nat :
      2 ^ Nat.log 2 (Params.t2 d) ≤ 2 ^ Params.b1 d := by
    rw [← t2_eq_two_pow_log d]
    exact hlarge.t2_le_pow_b1
  have hpowle_real :
      (2 : ℝ) ^ (Nat.log 2 (Params.t2 d) : ℕ) ≤
        (2 : ℝ) ^ (Params.b1 d : ℕ) := by
    exact_mod_cast hpowle_nat
  have hnonneg : 0 ≤ (2 : ℝ) ^ (-(Params.b1 d : ℝ)) := by positivity
  calc
    (2 : ℝ) ^ (Nat.log 2 (Params.t2 d) : ℕ) *
        (2 : ℝ) ^ (-(Params.b1 d : ℝ))
        ≤ (2 : ℝ) ^ (Params.b1 d : ℕ) *
            (2 : ℝ) ^ (-(Params.b1 d : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hpowle_real hnonneg
    _ = 1 := by
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          ring_nf
          norm_num

/-- Stage-2 complexity with the terminal one-copy gates and hard-seed copy
gates discharged by the Stage-1 and Stage-2 numeric wrappers. -/
theorem M2_complexity' (d : ℕ) (hpow : IsPow2 d)
    (hlog : 2 ^ 18 ≤ Nat.log 2 d)
    (hlarge : Checklist d)
    (hm0_le : (Classical.choose
        (hard_seed.{0} Params.jSurplus (by norm_num [Params.jSurplus])
          Params.delta (by norm_num [Params.delta])
          (by norm_num [Params.delta])) : ℕ) ≤ Nat.log 2 (Params.t2 d))
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d))
    (hxseed_le_one : M2_hard_seed_rowDensity d ≤ 1)
    (hrow_threshold :
      ⌈(2 : ℝ) ^ (Nat.log 2 (Params.r2 d) : ℕ) *
        M2_hard_seed_rowDensity d * (Fintype.card (C1 d) : ℝ)⌉₊
          ≤ Fintype.card (C1 d))
    (hseed_bridge : M2_hard_seed_columnDensity d ≤
      Params.h2 d *
        (2 : ℝ) ^ (-((M2_T d + D (M1T d) : ℕ) : ℝ)) /
          (1 + epsQT (Params.q2 d) (Params.t2 d)))
    (hy_three_fifths :
      ∀ c ≤ M2_T d + D (M1T d),
        (3 : ℝ) / 5 ≤
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c) :
    D (M2 d) = D (M1 d) + Nat.log 2 (Params.q2 d) := by
  have hlog256 : 256 ≤ Nat.log 2 d := by
    nlinarith
  have hT5 : 5 ≤ M2_T d := M2num_M2_T_ge_five d hlog256
  exact M2_complexity d hpow hlog256 hlarge hm0_le hr2pow
    (M2num_hard_seed_copy_lower d hT5)
    (M2num_hard_seed_copy_upper d hT5)
    hxseed_le_one hrow_threshold hseed_bridge
    (M1_terminal_density_le_one d)
    (M1_terminal_row_estimate d hpow hlog)
    (M1_terminal_col_estimate d)
    (M2num_residual_density_of_three_fifths d hy_three_fifths)

/-- Same as `M2_complexity'`, with the bridge supplied through the paper's
auxiliary density `h2'`. -/
theorem M2_complexity_h2prime (d : ℕ) (hpow : IsPow2 d)
    (hlog : 2 ^ 18 ≤ Nat.log 2 d)
    (hlarge : Checklist d)
    (hm0_le : (Classical.choose
        (hard_seed.{0} Params.jSurplus (by norm_num [Params.jSurplus])
          Params.delta (by norm_num [Params.delta])
          (by norm_num [Params.delta])) : ℕ) ≤ Nat.log 2 (Params.t2 d))
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d))
    (hrow_threshold :
      ⌈(2 : ℝ) ^ (Nat.log 2 (Params.r2 d) : ℕ) *
        M2_hard_seed_rowDensity d * (Fintype.card (C1 d) : ℝ)⌉₊
          ≤ Fintype.card (C1 d))
    (hraw : M2_hard_seed_to_h2prime_exp d)
    (hprime : M2_h2prime_bridge_exp d)
    (hy_three_fifths :
      ∀ c ≤ M2_T d + D (M1T d),
        (3 : ℝ) / 5 ≤
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c) :
    D (M2 d) = D (M1 d) + Nat.log 2 (Params.q2 d) := by
  exact M2_complexity' d hpow hlog hlarge hm0_le hr2pow
    (M2num_hard_seed_rowDensity_le_one d hlarge) hrow_threshold
    (M2num_hbridge_via_h2prime d hraw hprime)
    hy_three_fifths

-- CLAIM-END aux:m2-numerics

-- CLAIM-BEGIN aux:m2-robust-closed

private theorem M2num_robust_rowDensity_top_base (d : Nat)
    (hlarge : Checklist d)
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d)) :
    (2 : Real) ^ Nat.log 2 (Params.r2 d) *
        M2_hard_seed_rowDensity d =
      (Params.q2 d : Real) * (2 : Real) ^ (-(Params.b1 d : Real)) := by
  have hprod_nat :
      2 ^ Nat.log 2 (Params.r2 d) * 2 ^ Nat.log 2 (Params.t2 d) =
        Params.q2 d := by
    calc
      2 ^ Nat.log 2 (Params.r2 d) * 2 ^ Nat.log 2 (Params.t2 d)
          = Params.r2 d * Params.t2 d := by
            rw [M2num_log2_t2_eq_M2_T d, ← M2num_t2_eq_two_pow_M2_T d]
            rw [← hr2pow]
      _ = Params.q2 d := hlarge.q2_eq.symm
  have hprod_real :
      (2 : Real) ^ Nat.log 2 (Params.r2 d) *
          (2 : Real) ^ Nat.log 2 (Params.t2 d) =
        (Params.q2 d : Real) := by
    exact_mod_cast hprod_nat
  unfold M2_hard_seed_rowDensity
  calc
    (2 : Real) ^ Nat.log 2 (Params.r2 d) *
        ((2 : Real) ^ Nat.log 2 (Params.t2 d) *
          (2 : Real) ^ (-(Params.b1 d : Real)))
        =
      ((2 : Real) ^ Nat.log 2 (Params.r2 d) *
          (2 : Real) ^ Nat.log 2 (Params.t2 d)) *
        (2 : Real) ^ (-(Params.b1 d : Real)) := by ring
    _ = (Params.q2 d : Real) * (2 : Real) ^ (-(Params.b1 d : Real)) := by
      rw [hprod_real]

private theorem M2num_robust_eta2_eq_twice_base (d : Nat) :
    Params.eta2 d =
      (Params.q2 d : Real) *
        ((2 : Real) ^ (-(Params.b1 d : Real)) * 2) := by
  unfold Params.eta2
  rw [zpow_add₀ (by norm_num : (2 : Real) ≠ 0)]
  rw [zpow_one]
  rw [two_zpow_neg_nat_eq_rpow_neg_nat_stage2 (Params.b1 d)]

private theorem M2num_robust_top_rowDensity_le_eta2 (d : Nat)
    (hlarge : Checklist d)
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d)) :
    (2 : Real) ^ Nat.log 2 (Params.r2 d) *
        M2_hard_seed_rowDensity d <= Params.eta2 d := by
  rw [M2num_robust_rowDensity_top_base d hlarge hr2pow]
  rw [M2num_robust_eta2_eq_twice_base d]
  have hnonneg :
      0 <= (Params.q2 d : Real) *
        (2 : Real) ^ (-(Params.b1 d : Real)) := by
    positivity
  nlinarith

private theorem M2num_robust_eta2_le_one128 (d : Nat) (hpow : IsPow2 d)
    (hlog : 2 ^ 18 <= Nat.log 2 d) :
    Params.eta2 d <= (1 : Real) / 128 := by
  have hη := Params.eta2_le_pow (d := d) hpow (N := 7) (by omega)
  have hval : (2 : Real) ^ (-(7 : Int)) = (1 : Real) / 128 := by norm_num
  simpa [hval] using hη

private theorem M2num_robust_scaled_rowDensity_le_one128 (d Re : Nat)
    (hpow : IsPow2 d) (hlog : 2 ^ 18 <= Nat.log 2 d)
    (hlarge : Checklist d)
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d))
    (hRe : Re <= Nat.log 2 (Params.r2 d)) :
    (2 : Real) ^ Re * M2_hard_seed_rowDensity d <= (1 : Real) / 128 := by
  have hpow_le :
      (2 : Real) ^ Re <= (2 : Real) ^ Nat.log 2 (Params.r2 d) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 <= 2) hRe
  have hrd_nonneg : 0 <= M2_hard_seed_rowDensity d := by
    unfold M2_hard_seed_rowDensity
    positivity
  have hscaled :
      (2 : Real) ^ Re * M2_hard_seed_rowDensity d <=
        (2 : Real) ^ Nat.log 2 (Params.r2 d) *
          M2_hard_seed_rowDensity d := by
    exact mul_le_mul_of_nonneg_right hpow_le hrd_nonneg
  exact le_trans hscaled
    (le_trans (M2num_robust_top_rowDensity_le_eta2 d hlarge hr2pow)
      (M2num_robust_eta2_le_one128 d hpow hlog))

private theorem M2num_robust_copies_real_eq (d : Nat) (hT5 : 5 <= M2_T d) :
    (M2_hard_seed_copies d : Real) =
      (9 / 16 : Real) * ((2 ^ M2_T d : Nat) : Real) := by
  unfold M2_hard_seed_copies
  rw [M2num_log2_t2_eq_M2_T d]
  simp [Params.jSurplus]
  have hsplit : M2_T d = 5 + (M2_T d - 5) := by omega
  rw [hsplit, pow_add]
  norm_num
  ring

private theorem M2num_robust_lhs_top_coeff (d : Nat)
    (hlarge : Checklist d)
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d))
    (hT5 : 5 <= M2_T d) :
    ((2 ^ Nat.log 2 (Params.r2 d) * M2_hard_seed_copies d : Nat) : Real)
      <= (9 / 16 : Real) * (Params.q2 d : Real) := by
  have hqcast : 2 ^ (Nat.log 2 (Params.r2 d) + M2_T d) = Params.q2 d := by
    calc
      2 ^ (Nat.log 2 (Params.r2 d) + M2_T d)
          = 2 ^ Nat.log 2 (Params.r2 d) * 2 ^ M2_T d := by rw [pow_add]
      _ = Params.r2 d * Params.t2 d := by
        rw [← hr2pow, ← M2num_t2_eq_two_pow_M2_T d]
      _ = Params.q2 d := hlarge.q2_eq.symm
  rw [Nat.cast_mul, M2num_robust_copies_real_eq d hT5]
  have hpowprod :
      ((2 ^ Nat.log 2 (Params.r2 d) : Nat) : Real) *
          ((2 ^ M2_T d : Nat) : Real) =
        (Params.q2 d : Real) := by
    rw [← Nat.cast_mul, ← pow_add, hqcast]
  calc
    ((2 ^ Nat.log 2 (Params.r2 d) : Nat) : Real) *
        ((9 / 16 : Real) * ((2 ^ M2_T d : Nat) : Real))
        = (9 / 16 : Real) *
          (((2 ^ Nat.log 2 (Params.r2 d) : Nat) : Real) *
            ((2 ^ M2_T d : Nat) : Real)) := by ring
    _ = (9 / 16 : Real) * (Params.q2 d : Real) := by rw [hpowprod]
    _ <= (9 / 16 : Real) * (Params.q2 d : Real) := le_rfl

private theorem M2num_robust_lhs_mid_coeff (d : Nat)
    (hlarge : Checklist d)
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d))
    (hT5 : 5 <= M2_T d)
    (hR1 : 1 <= Nat.log 2 (Params.r2 d)) :
    ((2 ^ (Nat.log 2 (Params.r2 d) - 1) *
        M2_hard_seed_copies d : Nat) : Real)
      <= (9 / 32 : Real) * (Params.q2 d : Real) := by
  let R := Nat.log 2 (Params.r2 d)
  have hqcast : 2 ^ (R + M2_T d) = Params.q2 d := by
    calc
      2 ^ (R + M2_T d) = 2 ^ R * 2 ^ M2_T d := by rw [pow_add]
      _ = Params.r2 d * Params.t2 d := by
        dsimp [R]
        rw [← hr2pow, ← M2num_t2_eq_two_pow_M2_T d]
      _ = Params.q2 d := hlarge.q2_eq.symm
  have hpowprod :
      ((2 ^ R : Nat) : Real) * ((2 ^ M2_T d : Nat) : Real) =
        (Params.q2 d : Real) := by
    rw [← Nat.cast_mul, ← pow_add, hqcast]
  have hRsplit : R = 1 + (R - 1) := by omega
  have hprod_mid :
      ((2 ^ (R - 1) : Nat) : Real) * ((2 ^ M2_T d : Nat) : Real) =
        (Params.q2 d : Real) / 2 := by
    rw [← hpowprod]
    rw [hRsplit, pow_add]
    have hsub : 1 + (R - 1) - 1 = R - 1 := by omega
    rw [hsub]
    norm_num [Nat.cast_mul]
    ring
  rw [Nat.cast_mul, M2num_robust_copies_real_eq d hT5]
  dsimp [R] at hprod_mid
  calc
    ((2 ^ (Nat.log 2 (Params.r2 d) - 1) : Nat) : Real) *
        ((9 / 16 : Real) * ((2 ^ M2_T d : Nat) : Real))
        = (9 / 16 : Real) *
          (((2 ^ (Nat.log 2 (Params.r2 d) - 1) : Nat) : Real) *
            ((2 ^ M2_T d : Nat) : Real)) := by ring
    _ = (9 / 16 : Real) * ((Params.q2 d : Real) / 2) := by rw [hprod_mid]
    _ = (9 / 32 : Real) * (Params.q2 d : Real) := by ring
    _ <= (9 / 32 : Real) * (Params.q2 d : Real) := le_rfl

private theorem M2num_robust_lhs_low_coeff (d : Nat)
    (hlarge : Checklist d)
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d))
    (hT5 : 5 <= M2_T d)
    (hR2 : 2 <= Nat.log 2 (Params.r2 d)) :
    ((2 ^ (Nat.log 2 (Params.r2 d) - 2) *
        M2_hard_seed_copies d : Nat) : Real)
      <= (9 / 64 : Real) * (Params.q2 d : Real) := by
  let R := Nat.log 2 (Params.r2 d)
  have hqcast : 2 ^ (R + M2_T d) = Params.q2 d := by
    calc
      2 ^ (R + M2_T d) = 2 ^ R * 2 ^ M2_T d := by rw [pow_add]
      _ = Params.r2 d * Params.t2 d := by
        dsimp [R]
        rw [← hr2pow, ← M2num_t2_eq_two_pow_M2_T d]
      _ = Params.q2 d := hlarge.q2_eq.symm
  have hpowprod :
      ((2 ^ R : Nat) : Real) * ((2 ^ M2_T d : Nat) : Real) =
        (Params.q2 d : Real) := by
    rw [← Nat.cast_mul, ← pow_add, hqcast]
  have hRsplit : R = 2 + (R - 2) := by omega
  have hprod_low :
      ((2 ^ (R - 2) : Nat) : Real) * ((2 ^ M2_T d : Nat) : Real) =
        (Params.q2 d : Real) / 4 := by
    rw [← hpowprod]
    rw [hRsplit, pow_add]
    have hsub : 2 + (R - 2) - 2 = R - 2 := by omega
    rw [hsub]
    norm_num [Nat.cast_mul]
    ring
  rw [Nat.cast_mul, M2num_robust_copies_real_eq d hT5]
  dsimp [R] at hprod_low
  calc
    ((2 ^ (Nat.log 2 (Params.r2 d) - 2) : Nat) : Real) *
        ((9 / 16 : Real) * ((2 ^ M2_T d : Nat) : Real))
        = (9 / 16 : Real) *
          (((2 ^ (Nat.log 2 (Params.r2 d) - 2) : Nat) : Real) *
            ((2 ^ M2_T d : Nat) : Real)) := by ring
    _ = (9 / 16 : Real) * ((Params.q2 d : Real) / 4) := by rw [hprod_low]
    _ = (9 / 64 : Real) * (Params.q2 d : Real) := by ring
    _ <= (9 / 64 : Real) * (Params.q2 d : Real) := le_rfl

private theorem M2num_robust_six_mul_add_twelve_le_two_pow {n : Nat}
    (hn : 6 <= n) :
    6 * n + 12 <= 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge n 6 with hnsmall | hnbig
      · have hn5 : n = 5 := by omega
        subst hn5
        norm_num
      · have hih := ih hnbig
        have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
        rw [hpow]
        omega

private theorem M2num_robust_six_mul_le_two_pow_sub_two {k : Nat}
    (hk : 8 <= k) :
    6 * k <= 2 ^ (k - 2) := by
  have hn : 6 <= k - 2 := by omega
  have hmain := M2num_robust_six_mul_add_twelve_le_two_pow hn
  have hrewrite : 6 * k = 6 * (k - 2) + 12 := by omega
  rw [hrewrite]
  exact hmain

private theorem M2num_robust_Rlog_ge2 (d : Nat) (hpow : IsPow2 d)
    (hlog : 2 ^ 18 <= Nat.log 2 d) (hlarge : Checklist d)
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d)) :
    2 <= Nat.log 2 (Params.r2 d) := by
  obtain ⟨k, rfl⟩ := hpow
  have hk : 2 ^ 18 <= k := by
    simpa [log_two_pow] using hlog
  have hloglog : 1 <= Nat.log 2 (Nat.log 2 (2 ^ k)) := by
    rw [log_two_pow]
    exact Nat.log_pos (by norm_num) (by omega)
  have ht2_le : Params.t2 (2 ^ k) <= 6 * k := by
    have ht := Params.t2_le (d := 2 ^ k) hloglog
    simpa [log_two_pow] using ht
  have ht2_le_pow : Params.t2 (2 ^ k) <= 2 ^ (k - 2) :=
    le_trans ht2_le (M2num_robust_six_mul_le_two_pow_sub_two (by omega))
  have hT_le : M2_T (2 ^ k) <= k - 2 := by
    rw [M2num_t2_eq_two_pow_M2_T (2 ^ k)] at ht2_le_pow
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp ht2_le_pow
  have hsum := M2num_log2_q2_eq_log2_r2_add_log2_t2
    (2 ^ k) hlarge hr2pow
  have hleft : Nat.log 2 (Params.q2 (2 ^ k)) = k := by
    rw [hlarge.q2_eq_self, log_two_pow]
  rw [hleft, M2num_log2_t2_eq_M2_T (2 ^ k)] at hsum
  omega

private theorem M2num_robust_balance_real_top {q x : Real}
    (hq0 : 0 <= q) (hx : x <= (1 : Real) / 128) :
    (9 / 16 : Real) * q <=
      q * (((1 : Real) / 2 + Params.delta) - x) / (1 - x) := by
  have hden : 0 < 1 - x := by nlinarith
  have hbeta : (1 / 2 : Real) + Params.delta = 3 / 5 := by
    norm_num [Params.delta]
  rw [hbeta]
  rw [le_div_iff₀ hden]
  nlinarith

private theorem M2num_robust_balance_real_mid {q x : Real}
    (hq0 : 0 <= q) (hx : x <= (1 : Real) / 128) :
    (9 / 32 : Real) * q <=
      q * (((1 : Real) / 4 + Params.delta / 2) - x) / (1 - x) := by
  have hden : 0 < 1 - x := by nlinarith
  have hbeta : (1 / 4 : Real) + Params.delta / 2 = 3 / 10 := by
    norm_num [Params.delta]
  rw [hbeta]
  rw [le_div_iff₀ hden]
  nlinarith

private theorem M2num_robust_balance_real_low {q x : Real}
    (hq0 : 0 <= q) (hx : x <= (1 : Real) / 128) :
    (9 / 64 : Real) * q <=
      q * (((1 : Real) / 8 + Params.delta / 4) - x) / (1 - x) := by
  have hden : 0 < 1 - x := by nlinarith
  have hbeta : (1 / 8 : Real) + Params.delta / 4 = 3 / 20 := by
    norm_num [Params.delta]
  rw [hbeta]
  rw [le_div_iff₀ hden]
  nlinarith

private theorem M2num_robust_balance_top (d : Nat)
    (hpow : IsPow2 d) (hlog : 2 ^ 18 <= Nat.log 2 d)
    (hlarge : Checklist d)
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d))
    (hT5 : 5 <= M2_T d) :
    M2_robust_balance_gate d (Nat.log 2 (Params.r2 d))
      (1 / 2 + Params.delta) := by
  unfold M2_robust_balance_gate
  let x : Real :=
    (2 : Real) ^ Nat.log 2 (Params.r2 d) * M2_hard_seed_rowDensity d
  have hx : x <= (1 : Real) / 128 :=
    M2num_robust_scaled_rowDensity_le_one128 d (Nat.log 2 (Params.r2 d))
      hpow hlog hlarge hr2pow (le_refl _)
  have hlhs := M2num_robust_lhs_top_coeff d hlarge hr2pow hT5
  have hreal :
      ((2 ^ Nat.log 2 (Params.r2 d) *
          M2_hard_seed_copies d : Nat) : Real) <=
        (Params.q2 d : Real) *
          ((1 / 2 + Params.delta) - x) / (1 - x) := by
    exact le_trans hlhs
      (M2num_robust_balance_real_top (by positivity) hx)
  have hceil_real :
      ((2 ^ Nat.log 2 (Params.r2 d) *
          M2_hard_seed_copies d : Nat) : Real) <=
        (Nat.ceil ((Params.q2 d : Real) *
          ((1 / 2 + Params.delta) -
            (2 : Real) ^ Nat.log 2 (Params.r2 d) *
              M2_hard_seed_rowDensity d) /
          (1 - (2 : Real) ^ Nat.log 2 (Params.r2 d) *
              M2_hard_seed_rowDensity d)) : Real) := by
    exact le_trans (by simpa [x] using hreal) (Nat.le_ceil _)
  exact_mod_cast hceil_real

private theorem M2num_robust_balance_mid (d : Nat)
    (hpow : IsPow2 d) (hlog : 2 ^ 18 <= Nat.log 2 d)
    (hlarge : Checklist d)
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d))
    (hT5 : 5 <= M2_T d)
    (hRlog_ge2 : 2 <= Nat.log 2 (Params.r2 d)) :
    M2_robust_balance_gate d (Nat.log 2 (Params.r2 d) - 1)
      (1 / 4 + Params.delta / 2) := by
  unfold M2_robust_balance_gate
  let Re := Nat.log 2 (Params.r2 d) - 1
  let x : Real := (2 : Real) ^ Re * M2_hard_seed_rowDensity d
  have hRe : Re <= Nat.log 2 (Params.r2 d) := by
    dsimp [Re]
    omega
  have hx : x <= (1 : Real) / 128 :=
    M2num_robust_scaled_rowDensity_le_one128 d Re hpow hlog hlarge hr2pow hRe
  have hlhs := M2num_robust_lhs_mid_coeff d hlarge hr2pow hT5 (by omega)
  have hreal :
      ((2 ^ (Nat.log 2 (Params.r2 d) - 1) *
          M2_hard_seed_copies d : Nat) : Real) <=
        (Params.q2 d : Real) *
          ((1 / 4 + Params.delta / 2) - x) / (1 - x) := by
    exact le_trans hlhs
      (M2num_robust_balance_real_mid (by positivity) hx)
  have hceil_real :
      ((2 ^ (Nat.log 2 (Params.r2 d) - 1) *
          M2_hard_seed_copies d : Nat) : Real) <=
        (Nat.ceil ((Params.q2 d : Real) *
          ((1 / 4 + Params.delta / 2) -
            (2 : Real) ^ (Nat.log 2 (Params.r2 d) - 1) *
              M2_hard_seed_rowDensity d) /
          (1 - (2 : Real) ^ (Nat.log 2 (Params.r2 d) - 1) *
              M2_hard_seed_rowDensity d)) : Real) := by
    exact le_trans (by simpa [Re, x] using hreal) (Nat.le_ceil _)
  exact_mod_cast hceil_real

private theorem M2num_robust_balance_low (d : Nat)
    (hpow : IsPow2 d) (hlog : 2 ^ 18 <= Nat.log 2 d)
    (hlarge : Checklist d)
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d))
    (hT5 : 5 <= M2_T d)
    (hRlog_ge2 : 2 <= Nat.log 2 (Params.r2 d)) :
    M2_robust_balance_gate d (Nat.log 2 (Params.r2 d) - 2)
      (1 / 8 + Params.delta / 4) := by
  unfold M2_robust_balance_gate
  let Re := Nat.log 2 (Params.r2 d) - 2
  let x : Real := (2 : Real) ^ Re * M2_hard_seed_rowDensity d
  have hRe : Re <= Nat.log 2 (Params.r2 d) := by
    dsimp [Re]
    omega
  have hx : x <= (1 : Real) / 128 :=
    M2num_robust_scaled_rowDensity_le_one128 d Re hpow hlog hlarge hr2pow hRe
  have hlhs := M2num_robust_lhs_low_coeff d hlarge hr2pow hT5 hRlog_ge2
  have hreal :
      ((2 ^ (Nat.log 2 (Params.r2 d) - 2) *
          M2_hard_seed_copies d : Nat) : Real) <=
        (Params.q2 d : Real) *
          ((1 / 8 + Params.delta / 4) - x) / (1 - x) := by
    exact le_trans hlhs
      (M2num_robust_balance_real_low (by positivity) hx)
  have hceil_real :
      ((2 ^ (Nat.log 2 (Params.r2 d) - 2) *
          M2_hard_seed_copies d : Nat) : Real) <=
        (Nat.ceil ((Params.q2 d : Real) *
          ((1 / 8 + Params.delta / 4) -
            (2 : Real) ^ (Nat.log 2 (Params.r2 d) - 2) *
              M2_hard_seed_rowDensity d) /
          (1 - (2 : Real) ^ (Nat.log 2 (Params.r2 d) - 2) *
              M2_hard_seed_rowDensity d)) : Real) := by
    exact le_trans (by simpa [Re, x] using hreal) (Nat.le_ceil _)
  exact_mod_cast hceil_real

/-- Public Stage-2 robustness wrapper.  The remaining inputs are public gates
already used elsewhere in the Stage-2/Stage-3 endgame; the private
`M2_robust_balance_gate` hypotheses of `M2_robust` are discharged internally. -/
theorem M2_robust_closed (d : Nat) (hpow : IsPow2 d)
    (hlog : 2 ^ 18 <= Nat.log 2 d) (hlarge : Checklist d)
    (hm0_le : (Classical.choose
        (hard_seed.{0} Params.jSurplus (by norm_num [Params.jSurplus])
          Params.delta (by norm_num [Params.delta])
          (by norm_num [Params.delta])) : Nat) <= Nat.log 2 (Params.t2 d))
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d))
    (hrow_threshold :
      Nat.ceil ((2 : Real) ^ (Nat.log 2 (Params.r2 d) : Nat) *
        M2_hard_seed_rowDensity d * (Fintype.card (C1 d) : Real))
          <= Fintype.card (C1 d))
    (hraw : M2_hard_seed_to_h2prime_exp d)
    (hprime : M2_h2prime_bridge_exp d)
    (hy_three_fifths :
      forall c, c <= M2_T d + D (M1T d) ->
        (3 : Real) / 5 <=
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c) :
    IsRobust (fun (c : C2 d) (r : R2 d) => M2 d r c)
      Params.delta (Params.b2 d) := by
  have hlog256 : 256 <= Nat.log 2 d := by
    nlinarith
  have hT5 : 5 <= M2_T d := M2num_M2_T_ge_five d hlog256
  have hp1 : 2 ^ M2_T d <= 2 * M2_hard_seed_copies d :=
    M2num_hard_seed_copy_lower d hT5
  have hp2 : M2_hard_seed_copies d <= 2 ^ M2_T d :=
    M2num_hard_seed_copy_upper d hT5
  have hxseed_le_one : M2_hard_seed_rowDensity d <= 1 :=
    M2num_hard_seed_rowDensity_le_one d hlarge
  have hseed_bridge :
      M2_hard_seed_columnDensity d <=
        Params.h2 d *
          (2 : Real) ^ (-((M2_T d + D (M1T d) : Nat) : Real)) /
            (1 + epsQT (Params.q2 d) (Params.t2 d)) :=
    M2num_hbridge_via_h2prime d hraw hprime
  have hresidual_density :
      forall c, c <= M2_T d + D (M1T d) ->
        1 / 2 + Params.delta <=
            yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
              (Params.h2 d) c /\
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
              (Params.h2 d) c <= 1 :=
    M2num_residual_density_of_three_fifths d hy_three_fifths
  have hRlog_ge2 : 2 <= Nat.log 2 (Params.r2 d) :=
    M2num_robust_Rlog_ge2 d hpow hlog hlarge hr2pow
  have hx_top :
      (2 : Real) ^ Nat.log 2 (Params.r2 d) *
          M2_hard_seed_rowDensity d <= 1 / 2 + Params.delta := by
    have hxsmall :=
      M2num_robust_scaled_rowDensity_le_one128 d
        (Nat.log 2 (Params.r2 d)) hpow hlog hlarge hr2pow (le_refl _)
    exact le_trans hxsmall (by norm_num [Params.delta])
  have hx_mid :
      (2 : Real) ^ (Nat.log 2 (Params.r2 d) - 1) *
          M2_hard_seed_rowDensity d <= 1 / 4 + Params.delta / 2 := by
    have hxsmall :=
      M2num_robust_scaled_rowDensity_le_one128 d
        (Nat.log 2 (Params.r2 d) - 1) hpow hlog hlarge hr2pow (by omega)
    exact le_trans hxsmall (by norm_num [Params.delta])
  have hx_low :
      (2 : Real) ^ (Nat.log 2 (Params.r2 d) - 2) *
          M2_hard_seed_rowDensity d <= 1 / 8 + Params.delta / 4 := by
    have hxsmall :=
      M2num_robust_scaled_rowDensity_le_one128 d
        (Nat.log 2 (Params.r2 d) - 2) hpow hlog hlarge hr2pow (by omega)
    exact le_trans hxsmall (by norm_num [Params.delta])
  exact M2_robust d hpow hlog256 hlarge hm0_le hr2pow hp1 hp2
    hxseed_le_one hrow_threshold hseed_bridge
    (M1_terminal_density_le_one d)
    (M1_terminal_row_estimate d hpow hlog)
    (M1_terminal_col_estimate d)
    hresidual_density
    hRlog_ge2 hx_top hx_mid hx_low
    (M2num_robust_balance_top d hpow hlog hlarge hr2pow hT5)
    (M2num_robust_balance_mid d hpow hlog hlarge hr2pow hT5 hRlog_ge2)
    (M2num_robust_balance_low d hpow hlog hlarge hr2pow hT5 hRlog_ge2)

-- CLAIM-END aux:m2-robust-closed

end NPCC

namespace NPCC

open Finset
open Workspace.Types.Protocol
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace

-- CLAIM-BEGIN aux:m2-dense-code-family

abbrev M2DenseDepth (d : Nat) : Nat :=
  Nat.log 2 (Params.r2 d) + M2_T d

noncomputable abbrev M2DenseRin (d : Nat) :
    Finset (Fin (2 ^ M2DenseDepth d) × C1 d) :=
  Finset.univ

noncomputable abbrev M2DenseRows (d : Nat) : Type :=
  {a // a ∈ M2DenseRin d}

noncomputable abbrev M2DenseCols (d : Nat) (Sdense : Finset (C2 d)) : Type :=
  {c // c ∈ Sdense}

noncomputable abbrev M2DenseLoss (d : Nat) : Nat :=
  Nat.ceil ((2 : Real) ^ (1 - (Params.b1 d : Real)) *
    (Fintype.card (C1 d) : Real))

noncomputable abbrev M2DenseLabel (d : Nat) {B : Type*}
    (P : Protocol (M2DenseRows d) B Bool) :
    Fin (2 ^ M2DenseDepth d) × C1 d -> Fin (2 ^ M2DenseDepth d) :=
  Protocol.prefixLabelFinQ (M2DenseRin d) P

noncomputable abbrev M2DenseGame (d : Nat)
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (Sdense : Finset (C2 d)) :
    M2DenseRows d -> M2DenseCols d Sdense -> Bool :=
  subgame
    (relaxedInterlace (M1T d)
      (fun j gamma => S2fam d j (Fin.cast hqcast gamma)))
    (M2DenseRin d) Sdense

private theorem two_zpow_neg_nat_add_one_eq_rpow_one_sub_nat_stage2 (n : Nat) :
    (2 : Real) ^ (-(n : Int) + 1) =
      (2 : Real) ^ (1 - (n : Real)) := by
  have hcast : (((-(n : Int) + 1 : Int) : Real) = 1 - (n : Real)) := by
    norm_num
    ring
  rw [hcast.symm]
  exact (Real.rpow_intCast (2 : Real) (-(n : Int) + 1)).symm

private theorem M2DenseDepth_eq_log_q2 (d : Nat)
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d) :
    M2DenseDepth d = Nat.log 2 (Params.q2 d) := by
  rw [← hqcast]
  simp [M2DenseDepth]

private theorem M2DenseDepth_eq_clog_q2 (d : Nat) (hlarge : Checklist d)
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d) :
    M2DenseDepth d = Nat.clog 2 (Params.q2 d) := by
  rw [hlarge.clog_q2_eq]
  exact M2DenseDepth_eq_log_q2 d hqcast

private theorem M2Dense_YofCode_dense (d : Nat) (hlarge : Checklist d)
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (hgap : 2 ^ M2DenseDepth d * M2DenseLoss d < Fintype.card (C1 d))
    (Sdense : Finset (C2 d))
    (P : Protocol (M2DenseRows d) (M2DenseCols d Sdense) Bool)
    (hNW :
      NoWasteConclusion
        (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
        (M2DenseRin d)
        (M2DenseLabel d P)
        (Fintype.card (C1 d))
        (M2DenseLoss d))
    (j : Fin (2 ^ M2DenseDepth d)) :
    (1 - Params.eta2 d) * (Fintype.card (C1 d) : Real) <=
      ((Protocol.YofCode
        (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
        (M2DenseRin d) (M2DenseLabel d P) hNW (fun j => j) j).card : Real) := by
  classical
  let q := 2 ^ M2DenseDepth d
  let N := Fintype.card (C1 d)
  let loss := M2DenseLoss d
  let X := (2 : Real) ^ (1 - (Params.b1 d : Real)) * (N : Real)
  have hk_lt_N :
      (((Finset.univ : Finset (Fin q)).card - 1) * loss) < N := by
    have hcard :
        (Finset.univ : Finset (Fin q)).card = q := by simp
    have hle :
        (((Finset.univ : Finset (Fin q)).card - 1) * loss) <= q * loss := by
      rw [hcard]
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    exact lt_of_le_of_lt hle (by simpa [q, N, loss] using hgap)
  have hk_le_N :
      (((Finset.univ : Finset (Fin q)).card - 1) * loss) <= N :=
    Nat.le_of_lt hk_lt_N
  have hYnat :
      N - (((Finset.univ : Finset (Fin q)).card - 1) * loss) <=
        (Protocol.YofCode
          (Finset.univ : Finset (Fin q))
          (M2DenseRin d) (M2DenseLabel d P) hNW (fun j => j) j).card := by
    simpa [q, N, loss] using
      Protocol.YofCode_card_ge
        (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
        (M2DenseRin d) (M2DenseLabel d P) hNW (fun j => j) j
  have hcardQ :
      ((Finset.univ : Finset (Fin q)).card - 1 : Nat) = q - 1 := by
    simp [q]
  have hqpos : 1 <= q := by
    dsimp [q]
    exact Nat.one_le_two_pow
  have hqsub_cast : (((Finset.univ : Finset (Fin q)).card - 1 : Nat) : Real) =
      (q : Real) - 1 := by
    rw [hcardQ]
    rw [Nat.cast_sub hqpos]
    norm_num
  have hqsub_nonneg : 0 <= (q : Real) - 1 := by
    exact sub_nonneg.mpr (by exact_mod_cast hqpos)
  have hceil_lt : (loss : Real) < X + 1 := by
    dsimp [loss, X, N, M2DenseLoss]
    exact Nat.ceil_lt_add_one (by positivity)
  have hceil_le : (loss : Real) <= X + 1 := le_of_lt hceil_lt
  have hleft_le :
      (((Finset.univ : Finset (Fin q)).card - 1 : Nat) : Real) *
          (loss : Real) <=
        ((q : Real) - 1) * (X + 1) := by
    rw [hqsub_cast]
    exact mul_le_mul_of_nonneg_left hceil_le hqsub_nonneg
  have hslack :
      ((q : Real) - 1) * (X + 1) <
        Params.eta2 d * (N : Real) := by
    dsimp [q, X, N]
    have hpow :
        (2 : Real) ^ (-(Params.b1 d : Int) + 1) =
          (2 : Real) ^ (1 - (Params.b1 d : Real)) :=
      two_zpow_neg_nat_add_one_eq_rpow_one_sub_nat_stage2 (Params.b1 d)
    simpa [M2DenseDepth, C1, hpow, hqcast] using
      hlarge.dens_nondominant_slack
  have hloss_eta :
      (((Finset.univ : Finset (Fin q)).card - 1 : Nat) : Real) *
          (loss : Real) <
        Params.eta2 d * (N : Real) :=
    lt_of_le_of_lt hleft_le hslack
  have hsub_real :
      (((N - (((Finset.univ : Finset (Fin q)).card - 1) * loss)) : Nat) : Real) <=
        ((Protocol.YofCode
          (Finset.univ : Finset (Fin q))
          (M2DenseRin d) (M2DenseLabel d P) hNW (fun j => j) j).card : Real) := by
    exact_mod_cast hYnat
  have htarget :
      (1 - Params.eta2 d) * (N : Real) <=
        (((N - (((Finset.univ : Finset (Fin q)).card - 1) * loss)) : Nat) : Real) := by
    have hcastmul :
        (((((Finset.univ : Finset (Fin q)).card - 1) * loss) : Nat) : Real) =
          (((Finset.univ : Finset (Fin q)).card - 1 : Nat) : Real) *
            (loss : Real) := by norm_num
    rw [Nat.cast_sub hk_le_N]
    rw [hcastmul]
    nlinarith
  exact le_trans htarget hsub_real

structure M2SeparationTransposeDenseRowsCodeData
    (d : Nat) (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (Sdense : Finset (C2 d))
    (P : Protocol (M2DenseRows d) (M2DenseCols d Sdense) Bool) where
  first_row_bits :
    Protocol.FirstKRowBitsOn
      (Finset.univ : Finset (M2DenseRows d))
      (Finset.univ : Finset (M2DenseCols d Sdense))
      (M2DenseDepth d) P
  noWaste :
    NoWasteConclusion
      (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
      (M2DenseRin d)
      (M2DenseLabel d P)
      (Fintype.card (C1 d))
      (M2DenseLoss d)
  branch :
    Fin (2 ^ M2DenseDepth d) ->
      Protocol.BranchAt (Protocol.swap P)
        (fun c a => M2DenseGame d hqcast Sdense a c)
        (M2DenseDepth d)
  branch_sideTrace :
    forall j,
      (branch j).sideTrace =
        List.replicate (M2DenseDepth d) Protocol.ActualBitSide.bob
  depth_eq_log_q2 :
    M2DenseDepth d = Nat.log 2 (Params.q2 d)
  depth_eq_clog_q2 :
    M2DenseDepth d = Nat.clog 2 (Params.q2 d)
  alphaOfCode :
    Fin (2 ^ M2DenseDepth d) -> Fin (2 ^ M2DenseDepth d)
  alphaOfCode_eq :
    forall j,
      alphaOfCode j =
        Protocol.alphaOfCode
          (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
          (M2DenseRin d) (M2DenseLabel d P) noWaste (fun j => j) j
  YofCode :
    Fin (2 ^ M2DenseDepth d) -> Finset (C1 d)
  YofCode_eq :
    forall j,
      YofCode j =
        Protocol.YofCode
          (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
          (M2DenseRin d) (M2DenseLabel d P) noWaste (fun j => j) j
  YofCode_card_ge :
    forall j,
      Fintype.card (C1 d) -
          (((Finset.univ : Finset (Fin (2 ^ M2DenseDepth d))).card - 1) *
            M2DenseLoss d) <=
        (YofCode j).card
  YofCode_dense :
    forall j,
      (1 - Params.eta2 d) * (Fintype.card (C1 d) : Real) <=
        ((YofCode j).card : Real)
  S_rows_survive :
    forall j (c : C2 d) (hc : c ∈ Sdense),
      (⟨c, hc⟩ : M2DenseCols d Sdense) ∈ (branch j).rows
  diagonal_cols :
    forall j gamma, gamma ∈ YofCode j ->
      (⟨(alphaOfCode j, gamma), by simp [M2DenseRin]⟩ : M2DenseRows d) ∈
        (branch j).cols

theorem M2_separation_transpose_dense_rows_code_data (d : Nat) (hpow : IsPow2 d)
    (hlog256 : 256 <= Nat.log 2 d)
    (hlarge : Checklist d)
    (hm0_le : (Classical.choose
        (hard_seed.{0} Params.jSurplus (by norm_num [Params.jSurplus])
          Params.delta (by norm_num [Params.delta])
          (by norm_num [Params.delta])) : Nat) <= Nat.log 2 (Params.t2 d))
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d))
    (hp1 : 2 ^ M2_T d <= 2 * M2_hard_seed_copies d)
    (hp2 : M2_hard_seed_copies d <= 2 ^ M2_T d)
    (hxseed_le_one : M2_hard_seed_rowDensity d <= 1)
    (hrow_threshold :
      Nat.ceil ((2 : Real) ^ (Nat.log 2 (Params.r2 d) : Nat) *
        M2_hard_seed_rowDensity d * (Fintype.card (C1 d) : Real))
          <= Fintype.card (C1 d))
    (hseed_bridge : M2_hard_seed_columnDensity d <=
      Params.h2 d *
        (2 : Real) ^ (-((M2_T d + D (M1T d) : Nat) : Real)) /
          (1 + epsQT (Params.q2 d) (Params.t2 d)))
    (hy_le_one : M1_stage2_terminal_density d <= 1)
    (hrowTerm : 9 * Params.t1 d <=
      16 * Nat.ceil ((Fintype.card (R1 d) : Real) *
        M1_stage2_terminal_density d))
    (hcolTerm : (2 : Real) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : Int))
        * (Fintype.card (C1 d) : Real) <=
      (Nat.ceil ((Fintype.card (C1 d) : Real) *
        ((2 : Real) ^ (-(Params.b1 d : Int)))) : Real))
    (hresidual_density : forall c, c <= M2_T d + D (M1T d) ->
      1 / 2 + Params.delta <=
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c /\
        yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c <= 1)
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (sigma : Real) (hsigma0 : 0 < sigma) (hsigma1 : sigma <= 1)
    (hsigma_dense : 1 - 8 * Params.h2 d <= sigma)
    (hres_dense : IsColumnLossResilient (M1T d) (Params.b1 d : Real)
      (epsQT (Params.q2 d) (Params.t2 d))
      (Nat.log 2 (Params.q2 d)) (M2_T d) sigma)
    (hxseed_le_inv_r : M2_hard_seed_rowDensity d <=
      (2 : Real) ^ (-(Nat.log 2 (Params.r2 d) : Real)))
    (hseed_bridge_dense : M2_hard_seed_columnDensity d <=
      sigma *
        (2 : Real) ^ (-((M2_T d + D (M1T d) : Nat) : Real)) /
          (1 + epsQT (Params.q2 d) (Params.t2 d)))
    (hdelta_sep : Params.delta <= 1 / Real.sqrt 2 - 1 / 2)
    (hT1 : 1 <= M2_T d)
    (hgap :
      2 ^ M2DenseDepth d *
        Nat.ceil ((2 : Real) ^ (1 - (Params.b1 d : Real)) *
          (Fintype.card (C1 d) : Real)) < Fintype.card (C1 d))
    (Sdense : Finset (C2 d))
    (hSdense : sigma * (L2 d : Real) <= (Sdense.card : Real))
    (P : Protocol (M2DenseRows d) (M2DenseCols d Sdense) Bool)
    (hP : P.Computes (M2DenseGame d hqcast Sdense))
    (hcost : P.cost <= D (M2 d)) :
    Nonempty (M2SeparationTransposeDenseRowsCodeData d hqcast Sdense P) := by
  classical
  have hcore :=
    M2_separation_transpose_dense_rows d hpow hlog256 hlarge hm0_le hr2pow
      hp1 hp2 hxseed_le_one hrow_threshold hseed_bridge hy_le_one
      hrowTerm hcolTerm hresidual_density hqcast sigma hsigma0 hsigma1
      hsigma_dense hres_dense hxseed_le_inv_r hseed_bridge_dense
      hdelta_sep hT1 hgap Sdense hSdense P hP hcost
  rcases hcore with ⟨hfirst, hnw⟩
  have hL2pos_nat : 0 < L2 d := L2_pos d hlarge.t2_le_q2 hlarge.one_le_q1
  have hSdense_card_pos : 0 < Sdense.card := by
    have hprod : 0 < sigma * (L2 d : Real) := by
      exact mul_pos hsigma0 (by exact_mod_cast hL2pos_nat)
    have hcard_real : 0 < (Sdense.card : Real) := lt_of_lt_of_le hprod hSdense
    exact_mod_cast hcard_real
  have hcols : (Finset.univ : Finset (M2DenseCols d Sdense)).Nonempty := by
    obtain ⟨c, hc⟩ := Finset.card_pos.mp hSdense_card_pos
    exact ⟨⟨c, hc⟩, Finset.mem_univ _⟩
  have hlower_pos :
      0 < Fintype.card (C1 d) -
        (((Finset.univ : Finset (Fin (2 ^ M2DenseDepth d))).card - 1) *
          M2DenseLoss d) := by
    have hle :
        (((Finset.univ : Finset (Fin (2 ^ M2DenseDepth d))).card - 1) *
            M2DenseLoss d) <=
          2 ^ M2DenseDepth d * M2DenseLoss d := by
      have hcard :
          (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d))).card =
            2 ^ M2DenseDepth d := by simp
      have hsub :
          ((Finset.univ : Finset (Fin (2 ^ M2DenseDepth d))).card - 1) <=
            2 ^ M2DenseDepth d := by
        rw [hcard]
        exact Nat.sub_le _ _
      exact Nat.mul_le_mul_right _ hsub
    exact Nat.sub_pos_of_lt (lt_of_le_of_lt hle (by simpa [M2DenseLoss] using hgap))
  have hgap_loss :
      2 ^ M2DenseDepth d * M2DenseLoss d < Fintype.card (C1 d) := by
    simpa [M2DenseLoss] using hgap
  have hrow_nonempty :
      forall j : Fin (2 ^ M2DenseDepth d),
        (Protocol.rowPrefixRows (M2DenseDepth d) P j).Nonempty := by
    intro j
    let alpha :=
      Protocol.alphaOfCode
        (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
        (M2DenseRin d) (M2DenseLabel d P) hnw (fun j => j) j
    have hspec :=
      Protocol.alphaOfCode_spec
        (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
        (M2DenseRin d) (M2DenseLabel d P) hnw (fun j => j) j
    have hcard_pos :
        0 <
          ((M2DenseRin d).filter
            (fun p => M2DenseLabel d P p = j ∧ p.1 = alpha)).card :=
      lt_of_lt_of_le hlower_pos hspec.2.1
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard_pos
    rw [Finset.mem_filter] at hp
    rcases hp with ⟨hpR, hlabel, _halpha⟩
    refine ⟨⟨p, hpR⟩, ?_⟩
    rw [Protocol.rowPrefixRows, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    dsimp [M2DenseLabel, Protocol.prefixLabelFinQ] at hlabel
    simpa [hpR] using hlabel
  have hcolFirst :
      Protocol.FirstKColBitsOn
        (Finset.univ : Finset (M2DenseCols d Sdense))
        (Finset.univ : Finset (M2DenseRows d))
        (M2DenseDepth d) (Protocol.swap P) := by
    simpa [Protocol.FirstKColBitsOn, Protocol.swap_swap] using hfirst
  have hPswap :
      (Protocol.swap P).Computes
        (fun c a => M2DenseGame d hqcast Sdense a c) := by
    intro c a
    rw [Protocol.eval_swap]
    exact hP a c
  let brBob :
      Fin (2 ^ M2DenseDepth d) ->
        Protocol.BranchAt (Protocol.swap P)
          (fun c a => M2DenseGame d hqcast Sdense a c)
          (M2DenseDepth d) :=
    fun j =>
      Protocol.mkBranchAt_of_colPrefix (Protocol.swap P)
        (fun c a => M2DenseGame d hqcast Sdense a c)
        (M2DenseDepth d) j hcolFirst hPswap hcols
        (by
          simpa [Protocol.colPrefixCols, Protocol.swap_swap] using hrow_nonempty j)
  refine ⟨
    { first_row_bits := hfirst
      noWaste := hnw
      branch := brBob
      branch_sideTrace := ?_
      depth_eq_log_q2 := M2DenseDepth_eq_log_q2 d hqcast
      depth_eq_clog_q2 := M2DenseDepth_eq_clog_q2 d hlarge hqcast
      alphaOfCode := fun j =>
        Protocol.alphaOfCode
          (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
          (M2DenseRin d) (M2DenseLabel d P) hnw (fun j => j) j
      alphaOfCode_eq := ?_
      YofCode := fun j =>
        Protocol.YofCode
          (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
          (M2DenseRin d) (M2DenseLabel d P) hnw (fun j => j) j
      YofCode_eq := ?_
      YofCode_card_ge := ?_
      YofCode_dense := ?_
      S_rows_survive := ?_
      diagonal_cols := ?_ }⟩
  · intro j
    simp [brBob, Protocol.mkBranchAt_of_colPrefix, Protocol.branchAt_of_swap,
      Protocol.mkBranchAt_of_rowPrefix, Protocol.ActualBitSide.swap]
  · intro j
    rfl
  · intro j
    rfl
  · intro j
    exact
      Protocol.YofCode_card_ge
        (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
        (M2DenseRin d) (M2DenseLabel d P) hnw (fun j => j) j
  · intro j
    exact M2Dense_YofCode_dense d hlarge hqcast
      hgap_loss Sdense P hnw j
  · intro j c hc
    simp [brBob, Protocol.mkBranchAt_of_colPrefix, Protocol.branchAt_of_swap,
      Protocol.mkBranchAt_of_rowPrefix]
  · intro j gamma hgamma
    let alpha :=
      Protocol.alphaOfCode
        (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
        (M2DenseRin d) (M2DenseLabel d P) hnw (fun j => j) j
    change gamma ∈
      ((Finset.univ : Finset (C1 d)).filter
        (fun x => (alpha, x) ∈ M2DenseRin d ∧
          M2DenseLabel d P (alpha, x) = j)) at hgamma
    have hmem := Finset.mem_filter.mp hgamma
    have hRin : (alpha, gamma) ∈ M2DenseRin d := hmem.2.1
    have hlabel : M2DenseLabel d P (alpha, gamma) = j := hmem.2.2
    change (⟨(alpha, gamma), hRin⟩ : M2DenseRows d) ∈
      Protocol.colPrefixCols (M2DenseDepth d) (Protocol.swap P) j
    change (⟨(alpha, gamma), hRin⟩ : M2DenseRows d) ∈
      Protocol.rowPrefixRows (M2DenseDepth d) (Protocol.swap (Protocol.swap P)) j
    rw [Protocol.swap_swap]
    rw [Protocol.rowPrefixRows, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hfiber :
        (alpha, gamma) ∈
          Protocol.prefixFiber (M2DenseRin d)
            (Protocol.prefixLabelFinQ (M2DenseRin d) P) j := by
      rw [Protocol.prefixFiber, Finset.mem_filter]
      exact ⟨hRin, by simpa [M2DenseLabel] using hlabel⟩
    have hprefix :=
      (Protocol.prefixFiber_mem_iff (M2DenseRin d) P j (alpha, gamma)).mp
        hfiber
    rcases hprefix with ⟨ha, hcode⟩
    have hsub :
        (⟨(alpha, gamma), ha⟩ : M2DenseRows d) =
          ⟨(alpha, gamma), hRin⟩ := Subtype.ext rfl
    simpa [hsub] using hcode

-- CLAIM-END aux:m2-dense-code-family

-- CLAIM-BEGIN cor:M2SeparationTransposeDenseRows

private theorem M2Dense_row_fiber_card_eq_sum_label (d : Nat)
    (Sdense : Finset (C2 d))
    (P : Protocol (M2DenseRows d) (M2DenseCols d Sdense) Bool)
    (i : Fin (2 ^ M2DenseDepth d)) :
    ((M2DenseRin d).filter (fun p => p.1 = i)).card =
      ∑ j : Fin (2 ^ M2DenseDepth d),
        ((M2DenseRin d).filter
          (fun p => M2DenseLabel d P p = j ∧ p.1 = i)).card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (M2DenseRin d).filter (fun p => p.1 = i))
    (t := (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d))))
    (f := M2DenseLabel d P)
    (by intro a _; exact Finset.mem_univ (M2DenseLabel d P a))
  simpa [Finset.filter_filter, and_comm, and_left_comm, and_assoc] using h

private theorem M2Dense_row_fiber_card (d : Nat)
    (i : Fin (2 ^ M2DenseDepth d)) :
    ((M2DenseRin d).filter (fun p => p.1 = i)).card =
      Fintype.card (C1 d) := by
  classical
  rw [← Finset.card_univ]
  refine Finset.card_bij (fun p _hp => p.2) ?hmem ?hinj ?hsurj
  · intro p _hp
    exact Finset.mem_univ p.2
  · intro p hp q hq hpq
    rw [Finset.mem_filter] at hp hq
    rcases hp with ⟨_hpR, hpfirst⟩
    rcases hq with ⟨_hqR, hqfirst⟩
    cases p with
    | mk pi px =>
        cases q with
        | mk qi qx =>
            simp only at hpq hpfirst hqfirst
            subst px
            subst pi
            subst qi
            rfl
  · intro x _hx
    refine ⟨(i, x), ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨by simp [M2DenseRin], rfl⟩

private theorem M2Dense_alphaOfCode_surj_on_Q (d : Nat)
    (Sdense : Finset (C2 d))
    (P : Protocol (M2DenseRows d) (M2DenseCols d Sdense) Bool)
    (hNW :
      NoWasteConclusion
        (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
        (M2DenseRin d)
        (M2DenseLabel d P)
        (Fintype.card (C1 d))
        (M2DenseLoss d))
    (hgap : 2 ^ M2DenseDepth d * M2DenseLoss d < Fintype.card (C1 d)) :
    Protocol.alphaOfCode_surj_on_Q
      (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
      (M2DenseRin d) (M2DenseLabel d P) hNW
      (fun j : Fin (2 ^ M2DenseDepth d) => j) := by
  classical
  intro i hi
  by_contra hnone
  have hnot :
      ∀ j : Fin (2 ^ M2DenseDepth d),
        Protocol.alphaOfCode
          (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
          (M2DenseRin d) (M2DenseLabel d P) hNW
          (fun j : Fin (2 ^ M2DenseDepth d) => j) j ≠ i := by
    intro j hji
    exact hnone ⟨j, hji⟩
  have hlt :
      ∀ j : Fin (2 ^ M2DenseDepth d),
        ((M2DenseRin d).filter
          (fun p => M2DenseLabel d P p = j ∧ p.1 = i)).card <
            M2DenseLoss d := by
    intro j
    have hspec :=
      Protocol.alphaOfCode_spec
        (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
        (M2DenseRin d) (M2DenseLabel d P) hNW
        (fun j : Fin (2 ^ M2DenseDepth d) => j) j
    exact hspec.2.2 i hi (by
      intro hia
      exact hnot j hia.symm)
  have hnonempty :
      (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d))).Nonempty := by
    exact ⟨⟨0, Nat.two_pow_pos (M2DenseDepth d)⟩, Finset.mem_univ _⟩
  have hsum_lt :
      (∑ j : Fin (2 ^ M2DenseDepth d),
        ((M2DenseRin d).filter
          (fun p => M2DenseLabel d P p = j ∧ p.1 = i)).card)
        <
      ∑ _j : Fin (2 ^ M2DenseDepth d), M2DenseLoss d := by
    exact Finset.sum_lt_sum_of_nonempty hnonempty
      (by intro j _hj; exact hlt j)
  have hsum_loss :
      (∑ _j : Fin (2 ^ M2DenseDepth d), M2DenseLoss d) =
        2 ^ M2DenseDepth d * M2DenseLoss d := by
    simp [Finset.sum_const]
  have hrow_sum := M2Dense_row_fiber_card_eq_sum_label d Sdense P i
  have hrow_card := M2Dense_row_fiber_card d i
  have hN_eq_sum :
      Fintype.card (C1 d) =
        ∑ j : Fin (2 ^ M2DenseDepth d),
          ((M2DenseRin d).filter
            (fun p => M2DenseLabel d P p = j ∧ p.1 = i)).card := by
    exact hrow_card.symm.trans hrow_sum
  have hN_lt : Fintype.card (C1 d) <
      2 ^ M2DenseDepth d * M2DenseLoss d := by
    rw [hN_eq_sum, ← hsum_loss]
    exact hsum_lt
  exact (not_lt_of_ge (Nat.le_of_lt hgap)) hN_lt

structure M2SeparationTransposeDenseRowsAlphaData
    (d : Nat) (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (Sdense : Finset (C2 d))
    (P : Protocol (M2DenseRows d) (M2DenseCols d Sdense) Bool) where
  first_row_bits :
    Protocol.FirstKRowBitsOn
      (Finset.univ : Finset (M2DenseRows d))
      (Finset.univ : Finset (M2DenseCols d Sdense))
      (M2DenseDepth d) P
  noWaste :
    NoWasteConclusion
      (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
      (M2DenseRin d)
      (M2DenseLabel d P)
      (Fintype.card (C1 d))
      (M2DenseLoss d)
  alphaOfCode_surj :
    Protocol.alphaOfCode_surj_on_Q
      (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
      (M2DenseRin d) (M2DenseLabel d P) noWaste
      (fun j : Fin (2 ^ M2DenseDepth d) => j)
  codeOfAlpha :
    Fin (Params.q2 d) -> Fin (2 ^ M2DenseDepth d)
  alphaOf_codeOfAlpha :
    forall alpha,
      Protocol.alphaOfCode
          (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
          (M2DenseRin d) (M2DenseLabel d P) noWaste
          (fun j : Fin (2 ^ M2DenseDepth d) => j)
          (codeOfAlpha alpha) =
        Fin.cast hqcast.symm alpha
  branch :
    Fin (Params.q2 d) ->
      Protocol.BranchAt (Protocol.swap P)
        (fun c a => M2DenseGame d hqcast Sdense a c)
        (M2DenseDepth d)
  branch_sideTrace :
    forall alpha,
      (branch alpha).sideTrace =
        List.replicate (M2DenseDepth d) Protocol.ActualBitSide.bob
  depth_eq_log_q2 :
    M2DenseDepth d = Nat.log 2 (Params.q2 d)
  depth_eq_clog_q2 :
    M2DenseDepth d = Nat.clog 2 (Params.q2 d)
  Yalpha :
    Fin (Params.q2 d) -> Finset (C1 d)
  Yalpha_eq :
    forall alpha,
      Yalpha alpha =
        Protocol.YofCode
          (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
          (M2DenseRin d) (M2DenseLabel d P) noWaste
          (fun j : Fin (2 ^ M2DenseDepth d) => j)
          (codeOfAlpha alpha)
  Yalpha_dense :
    forall alpha,
      (1 - Params.eta2 d) * (Fintype.card (C1 d) : Real) <=
        ((Yalpha alpha).card : Real)
  S_rows_survive :
    forall alpha (c : C2 d) (hc : c ∈ Sdense),
      (⟨c, hc⟩ : M2DenseCols d Sdense) ∈ (branch alpha).rows
  diagonal_cols :
    forall alpha gamma, gamma ∈ Yalpha alpha ->
      (⟨(Fin.cast hqcast.symm alpha, gamma), by simp [M2DenseRin]⟩ :
        M2DenseRows d) ∈ (branch alpha).cols

theorem M2_separation_transpose_dense_rows_alpha (d : Nat) (hpow : IsPow2 d)
    (hlog256 : 256 <= Nat.log 2 d)
    (hlarge : Checklist d)
    (hm0_le : (Classical.choose
        (hard_seed.{0} Params.jSurplus (by norm_num [Params.jSurplus])
          Params.delta (by norm_num [Params.delta])
          (by norm_num [Params.delta])) : Nat) <= Nat.log 2 (Params.t2 d))
    (hr2pow : Params.r2 d = 2 ^ Nat.log 2 (Params.r2 d))
    (hp1 : 2 ^ M2_T d <= 2 * M2_hard_seed_copies d)
    (hp2 : M2_hard_seed_copies d <= 2 ^ M2_T d)
    (hxseed_le_one : M2_hard_seed_rowDensity d <= 1)
    (hrow_threshold :
      Nat.ceil ((2 : Real) ^ (Nat.log 2 (Params.r2 d) : Nat) *
        M2_hard_seed_rowDensity d * (Fintype.card (C1 d) : Real))
          <= Fintype.card (C1 d))
    (hseed_bridge : M2_hard_seed_columnDensity d <=
      Params.h2 d *
        (2 : Real) ^ (-((M2_T d + D (M1T d) : Nat) : Real)) /
          (1 + epsQT (Params.q2 d) (Params.t2 d)))
    (hy_le_one : M1_stage2_terminal_density d <= 1)
    (hrowTerm : 9 * Params.t1 d <=
      16 * Nat.ceil ((Fintype.card (R1 d) : Real) *
        M1_stage2_terminal_density d))
    (hcolTerm : (2 : Real) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : Int))
        * (Fintype.card (C1 d) : Real) <=
      (Nat.ceil ((Fintype.card (C1 d) : Real) *
        ((2 : Real) ^ (-(Params.b1 d : Int)))) : Real))
    (hresidual_density : forall c, c <= M2_T d + D (M1T d) ->
      1 / 2 + Params.delta <=
          yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c /\
        yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d)
            (Params.h2 d) c <= 1)
    (hqcast : 2 ^ M2DenseDepth d = Params.q2 d)
    (sigma : Real) (hsigma0 : 0 < sigma) (hsigma1 : sigma <= 1)
    (hsigma_dense : 1 - 8 * Params.h2 d <= sigma)
    (hres_dense : IsColumnLossResilient (M1T d) (Params.b1 d : Real)
      (epsQT (Params.q2 d) (Params.t2 d))
      (Nat.log 2 (Params.q2 d)) (M2_T d) sigma)
    (hxseed_le_inv_r : M2_hard_seed_rowDensity d <=
      (2 : Real) ^ (-(Nat.log 2 (Params.r2 d) : Real)))
    (hseed_bridge_dense : M2_hard_seed_columnDensity d <=
      sigma *
        (2 : Real) ^ (-((M2_T d + D (M1T d) : Nat) : Real)) /
          (1 + epsQT (Params.q2 d) (Params.t2 d)))
    (hdelta_sep : Params.delta <= 1 / Real.sqrt 2 - 1 / 2)
    (hT1 : 1 <= M2_T d)
    (hgap :
      2 ^ M2DenseDepth d *
        Nat.ceil ((2 : Real) ^ (1 - (Params.b1 d : Real)) *
          (Fintype.card (C1 d) : Real)) < Fintype.card (C1 d))
    (Sdense : Finset (C2 d))
    (hSdense : sigma * (L2 d : Real) <= (Sdense.card : Real))
    (P : Protocol (M2DenseRows d) (M2DenseCols d Sdense) Bool)
    (hP : P.Computes (M2DenseGame d hqcast Sdense))
    (hcost : P.cost <= D (M2 d)) :
    Nonempty (M2SeparationTransposeDenseRowsAlphaData d hqcast Sdense P) := by
  classical
  obtain ⟨codeData⟩ :=
    M2_separation_transpose_dense_rows_code_data d hpow hlog256 hlarge
      hm0_le hr2pow hp1 hp2 hxseed_le_one hrow_threshold hseed_bridge
      hy_le_one hrowTerm hcolTerm hresidual_density hqcast sigma hsigma0
      hsigma1 hsigma_dense hres_dense hxseed_le_inv_r hseed_bridge_dense
      hdelta_sep hT1 hgap Sdense hSdense P hP hcost
  have hgap_loss :
      2 ^ M2DenseDepth d * M2DenseLoss d < Fintype.card (C1 d) := by
    simpa [M2DenseLoss] using hgap
  let hsurj :=
    M2Dense_alphaOfCode_surj_on_Q d Sdense P codeData.noWaste hgap_loss
  let codeOf : Fin (Params.q2 d) -> Fin (2 ^ M2DenseDepth d) :=
    fun alpha =>
      Protocol.codeOfAlpha
        (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
        (M2DenseRin d) (M2DenseLabel d P) codeData.noWaste
        (fun j : Fin (2 ^ M2DenseDepth d) => j) hsurj
        (Fin.cast hqcast.symm alpha) (by simp)
  refine ⟨
    { first_row_bits := codeData.first_row_bits
      noWaste := codeData.noWaste
      alphaOfCode_surj := hsurj
      codeOfAlpha := codeOf
      alphaOf_codeOfAlpha := ?_
      branch := fun alpha => codeData.branch (codeOf alpha)
      branch_sideTrace := ?_
      depth_eq_log_q2 := codeData.depth_eq_log_q2
      depth_eq_clog_q2 := codeData.depth_eq_clog_q2
      Yalpha := fun alpha => codeData.YofCode (codeOf alpha)
      Yalpha_eq := ?_
      Yalpha_dense := ?_
      S_rows_survive := ?_
      diagonal_cols := ?_ }⟩
  · intro alpha
    dsimp [codeOf]
    exact
      Protocol.alphaOf_codeOfAlpha
        (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
        (M2DenseRin d) (M2DenseLabel d P) codeData.noWaste
        (fun j : Fin (2 ^ M2DenseDepth d) => j) hsurj
        (Fin.cast hqcast.symm alpha) (by simp)
  · intro alpha
    exact codeData.branch_sideTrace (codeOf alpha)
  · intro alpha
    rw [codeData.YofCode_eq]
  · intro alpha
    exact codeData.YofCode_dense (codeOf alpha)
  · intro alpha c hc
    exact codeData.S_rows_survive (codeOf alpha) c hc
  · intro alpha gamma hgamma
    have hcol := codeData.diagonal_cols (codeOf alpha) gamma hgamma
    have hAlpha :
        codeData.alphaOfCode (codeOf alpha) = Fin.cast hqcast.symm alpha := by
      rw [codeData.alphaOfCode_eq]
      dsimp [codeOf]
      exact
        Protocol.alphaOf_codeOfAlpha
          (Finset.univ : Finset (Fin (2 ^ M2DenseDepth d)))
          (M2DenseRin d) (M2DenseLabel d P) codeData.noWaste
          (fun j : Fin (2 ^ M2DenseDepth d) => j) hsurj
          (Fin.cast hqcast.symm alpha) (by simp)
    simpa [hAlpha] using hcol

-- CLAIM-END cor:M2SeparationTransposeDenseRows

end NPCC
