import Mathlib
import NPCC.Defs
import NPCC.Relaxed
import NPCC.Upper
import NPCC.VBP
import NPCC.Engine
import NPCC.Transfer
import NPCC.SeedRank
import NPCC.LargeD

/-! # Stage-1 threshold calibration

The local games `Hlocal` exhibit the one-bit threshold later used by the
reduction: the game on `2^a` active blocks costs `a+1`, while the game on
`2^a+1` blocks costs `a+2`. Upper bounds identify row behaviours; lower bounds
follow a heavy protocol path and apply balanced-rectangle counting.

The dense and chosen-coordinate variants show that this threshold survives the
column losses and coordinate selections made by later stages. In particular,
`stage1_chosen_dense_threshold` applies to every injectively enumerated set of
at least `2^a+1` coordinates, not merely an initial segment. The Lean carrier
uses `q1+5`; `Params.two_pow_a` proves that this is the paper's `2^a+3` in the
large-parameter regime. -/

namespace NPCC

open Workspace.Types.CommComplexity
open Workspace.Types.Protocol

-- CLAIM-BEGIN def:H-local
/-- Paper `sec:control`, paragraph "Local Stage 1 threshold" (paragraph-level
def, no label): the local threshold games `𝓗_r(T)`. For an ARBITRARY indexed
column family `T : Fin L → (Fin (q₁+5) → Fin 2)` over the seed alphabet
`Cols(M₀) = Fin 2` (arbitrariness is load-bearing: the dense variants feed in
subfamilies `S' ⊆ S₁`, which are NOT balanced) and any `r ≤ q₁+5`, `𝓗_r(T)`
is the restriction of the full `(q₁+5)`-coordinate relaxed interlace
`⟨M₀⟩^{q₁+5, T}` to its first `r` outer row blocks — ALL columns (family
indices) kept, rows embedded through `Fin.castLE` exactly as `M₁` embeds
through `baseIdx` (never a raw ℕ offset).

The ambient coordinate count is
`Params.q1 d + 5` — definitionally the carrier of `S1fam`/`M1hat`, so
`𝓗_{q₁+5}(C₁) = M̂₁` and `𝓗_{q₁}(C₁) = M₁` hold by `rfl` — not the paper's
`2^a+3`, which equals it only propositionally under `2 ≤ d`
(`Params.two_pow_a`). Likewise the threshold rows enter downstream as
`r = q₁+2` (`= 2^a`) and `r = q₁+3` (`= 2^a+1`): both are underflow-free and
in range for EVERY `d`, so no consumer ever writes `2^a − c`. The paper's
lower end `1 ≤ r` is a use-site hypothesis, not baked in (`r = 0` is the
harmless empty-row degenerate). -/
def Hlocal (d : ℕ) {L : ℕ} (T : Fin L → Fin (Params.q1 d + 5) → Fin 2)
    (r : ℕ) (hr : r ≤ Params.q1 d + 5) :
    (Fin r × Fin 1) → Fin L → Bool :=
  fun a j => relaxedInterlace M0 T (Fin.castLE hr a.1, a.2) j
-- CLAIM-END def:H-local

/-- Companion: evaluation — `𝓗_r(T)` reads the seed at the family entry of
the castLE-embedded coordinate (definitional transparency, mirroring
`M1_apply`). -/
theorem Hlocal_apply (d : ℕ) {L : ℕ}
    (T : Fin L → Fin (Params.q1 d + 5) → Fin 2)
    (r : ℕ) (hr : r ≤ Params.q1 d + 5) (a : Fin r × Fin 1) (j : Fin L) :
    Hlocal d T r hr a j = M0 a.2 (T j (Fin.castLE hr a.1)) := rfl

/-- Companion: at full range `r = q₁+5` the local game IS the relaxed
interlace of the seed by `T` (the castLE embedding is the identity). -/
theorem Hlocal_full (d : ℕ) {L : ℕ}
    (T : Fin L → Fin (Params.q1 d + 5) → Fin 2) :
    Hlocal d T (Params.q1 d + 5) le_rfl = relaxedInterlace M0 T := rfl

/-- Companion: at the scaffold family and full range, `𝓗_{q₁+5}(C₁) = M̂₁` —
definitionally, because the coordinate carrier is spelled `q₁+5`. -/
theorem Hlocal_S1fam_full (d : ℕ) :
    Hlocal d (S1fam d) (Params.q1 d + 5) le_rfl = M1hat d := rfl

/-- Companion: at the scaffold family and `r = q₁`, the local game IS `M₁` —
the `Fin.castLE` restriction agrees definitionally with the `baseIdx`
(`Fin.castAdd`) pattern of `def:stage-matrices`. -/
theorem Hlocal_S1fam_q1 (d : ℕ) :
    Hlocal d (S1fam d) (Params.q1 d) (Nat.le_add_right _ 5) = M1 d := rfl

/-- Companion for `cor:M1-complexity`: the direct row-identification protocol
for the Stage-1 matrix. Alice announces the base coordinate using `a` bits
(`q₁ ≤ 2^a`), then Bob answers the seed bit. -/
theorem M1_upper_bound (d : ℕ) (hd : 2 ≤ d) :
    D (M1 d) ≤ Params.a d + 1 := by
  have hle : Params.q1 d ≤ 2 ^ Params.a d := by
    have h := Params.two_pow_a hd
    omega
  refine comp_le_of_row_types_succ (M1 d) (Params.a d)
    (fun p : R1 d => Fin.castLE hle p.1) ?_
  intro x1 x2 hτ
  have hfirst : x1.1 = x2.1 := by
    apply Fin.ext
    have hv := congrArg (fun x : Fin (2 ^ Params.a d) => x.val) hτ
    simpa using hv
  have hsecond : x1.2 = x2.2 := Subsingleton.elim _ _
  have hrow : x1 = x2 := Prod.ext hfirst hsecond
  rw [hrow]

/-- Companion for `cor:M1-complexity`: when the large-`d` divisibility gate
`q₁+2 = r₁·t₁` is available, the capacity exponent splits as
`a = log r₁ + log t₁`. -/
theorem M1_capacity_log_identity (d : ℕ) (hd : 2 ≤ d)
    (hdiv : Params.q1 d + 2 = Params.r1 d * Params.t1 d) :
    Params.a d = Nat.log 2 (Params.r1 d) + Nat.log 2 (Params.t1 d) := by
  have ht1_clog : Params.t1 d = 2 ^ Nat.clog 2 (64 * Nat.log 2 d) := rfl
  have ht1pow : Params.t1 d = 2 ^ Nat.log 2 (Params.t1 d) := by
    rw [ht1_clog, log_two_pow]
  have hqpow : Params.q1 d + 2 = 2 ^ Params.a d := (Params.two_pow_a hd).symm
  have hr1dvd : Dvd.dvd (Params.r1 d) (2 ^ Params.a d) := by
    rw [hqpow.symm]
    exact ⟨Params.t1 d, hdiv⟩
  obtain ⟨j, _hjle, hr1j⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hr1dvd
  have hr1pow : Params.r1 d = 2 ^ Nat.log 2 (Params.r1 d) := by
    rw [hr1j, log_two_pow]
  apply Nat.pow_right_injective (a := 2) (by norm_num : 2 ≤ 2)
  calc 2 ^ Params.a d = Params.q1 d + 2 := Params.two_pow_a hd
    _ = Params.r1 d * Params.t1 d := hdiv
    _ = 2 ^ Nat.log 2 (Params.r1 d) * 2 ^ Nat.log 2 (Params.t1 d) := by
        rw [hr1pow.symm, ht1pow.symm]
    _ = 2 ^ (Nat.log 2 (Params.r1 d) + Nat.log 2 (Params.t1 d)) := by rw [pow_add]

/-- Companion (restriction compatibility, the carrier of the subgame
monotonicity used by `rem:stage1-relative-threshold`): for `r ≤ r'`, the
smaller local game reads the larger one along `Fin.castLE`. -/
theorem Hlocal_castLE (d : ℕ) {L : ℕ}
    (T : Fin L → Fin (Params.q1 d + 5) → Fin 2)
    {r r' : ℕ} (h : r ≤ r') (hr' : r' ≤ Params.q1 d + 5)
    (a : Fin r × Fin 1) (j : Fin L) :
    Hlocal d T r (le_trans h hr') a j
      = Hlocal d T r' hr' (Fin.castLE h a.1, a.2) j := rfl

/-- Companion (gated spelling bridge): under `2 ≤ d` the ambient coordinate
count `q₁+5` is the paper's `2^a+3`. -/
theorem q1_add_five_eq {d : ℕ} (hd : 2 ≤ d) :
    Params.q1 d + 5 = 2 ^ Params.a d + 3 := by
  have h := Params.two_pow_a hd
  omega

/-- Companion (gated spelling bridge): the capacity threshold row count —
`q₁+2` IS the paper's `2^a`. The left side never underflows; the identity
(not a subtraction) carries the `2^a` spelling. -/
theorem q1_add_two_eq {d : ℕ} (hd : 2 ≤ d) :
    Params.q1 d + 2 = 2 ^ Params.a d :=
  (Params.two_pow_a hd).symm

/-- Companion (gated spelling bridge): the overload threshold row count —
`q₁+3` IS the paper's `2^a+1` (the `a+1 → a+2` jump row of the risk
ledger). -/
theorem q1_add_three_eq {d : ℕ} (hd : 2 ≤ d) :
    Params.q1 d + 3 = 2 ^ Params.a d + 1 := by
  have h := Params.two_pow_a hd
  omega

/-- Companion: the capacity game `𝓗_{2^a}(S₁)` of `lem:stage1-threshold`,
spelled underflow-free as `r := q₁+2` (in range for EVERY `d`; equal to the
paper's `2^a` under `2 ≤ d` by `q1_add_two_eq`). Its complexity is the
capacity budget `B_cap` of the NO-case argument. -/
noncomputable def Hcap (d : ℕ) :
    (Fin (Params.q1 d + 2) × Fin 1) → C1 d → Bool :=
  Hlocal d (S1fam d) (Params.q1 d + 2) (by omega)

/-- Companion: the overload game `𝓗_{2^a+1}(S₁)` of `lem:stage1-threshold`,
spelled `r := q₁+3` (the paper's `2^a+1` under `2 ≤ d` by
`q1_add_three_eq`). -/
noncomputable def Hover (d : ℕ) :
    (Fin (Params.q1 d + 3) × Fin 1) → C1 d → Bool :=
  Hlocal d (S1fam d) (Params.q1 d + 3) (by omega)

/-- Companion (chosen-coordinate form, feeding
`cor:stage1-chosen-dense-threshold`): the local game at an ARBITRARY tuple of
outer coordinates `e : Fin u → Fin (q₁+5)`. The corollary quantifies over
EVERY `Q ⊆ [2^a+3]` with `|Q| ≥ 2^a+1`; a `Q` enters here through an
enumeration `e` (injectivity is a use-site hypothesis, mirroring
`relaxed_to_classical`), so the quantification is genuinely over all `Q`,
never just initial segments. -/
def HlocalAt (d : ℕ) {L : ℕ} (T : Fin L → Fin (Params.q1 d + 5) → Fin 2)
    {u : ℕ} (e : Fin u → Fin (Params.q1 d + 5)) :
    (Fin u × Fin 1) → Fin L → Bool :=
  fun a j => relaxedInterlace M0 T (e a.1, a.2) j

/-- Companion: `𝓗_r(T)` is the chosen-coordinate game at the initial-segment
enumeration `Fin.castLE hr`. -/
theorem Hlocal_eq_HlocalAt (d : ℕ) {L : ℕ}
    (T : Fin L → Fin (Params.q1 d + 5) → Fin 2)
    (r : ℕ) (hr : r ≤ Params.q1 d + 5) :
    Hlocal d T r hr = HlocalAt d T (Fin.castLE hr) := rfl

/-- Companion: the seed row `[1 0]` determines the unique `Fin 2` column
matching a Boolean output. -/
private theorem stage1_fin2_of_M0 (x : Fin 1) (y : Fin 2) (z : Bool)
    (h : M0 x y = z) : y = (if z then 0 else 1) := by
  fin_cases y <;> cases z <;> simp [M0] at h ⊢

/-- Companion: a deterministic protocol has a heavy monochromatic leaf
rectangle. The counters `u` and `v` record the Alice and Bob bits spent along
the selected root-to-leaf path. -/
theorem protocol_exists_heavy_rectangle {A B Z : Type*}
    (P : Protocol A B Z) (R : Finset A) (C : Finset B) :
    ∃ (R' : Finset A) (C' : Finset B) (u v : ℕ) (z : Z),
      R' ⊆ R ∧ C' ⊆ C ∧ u + v ≤ P.cost ∧
      R.card ≤ 2 ^ u * R'.card ∧ C.card ≤ 2 ^ v * C'.card ∧
      ∀ a ∈ R', ∀ b ∈ C', P.eval a b = z := by
  classical
  induction P generalizing R C with
  | leaf z =>
      refine ⟨R, C, 0, 0, z, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact subset_rfl
      · exact subset_rfl
      · simp [Protocol.cost]
      · simp
      · simp
      · intro a _ b _
        rfl
  | aNode f l r ihl ihr =>
      set Rt : Finset A := R.filter (fun x => f x = true) with hRt
      set Rf : Finset A := R.filter (fun x => ¬ f x = true) with hRf
      have hcardsum : Rt.card + Rf.card = R.card := by
        rw [hRt, hRf]
        exact Finset.card_filter_add_card_filter_not
          (s := R) (p := fun x => f x = true)
      by_cases hhalf : Rf.card ≤ Rt.card
      · obtain ⟨R', C', u, v, z, hR', hC', huv, hrow, hcol, hmono⟩ := ihr Rt C
        refine ⟨R', C', u + 1, v, z, ?_, hC', ?_, ?_, hcol, ?_⟩
        · intro a ha
          exact (Finset.mem_filter.mp (hR' ha)).1
        · simp only [Protocol.cost]
          omega
        · have hheavy : R.card ≤ 2 * Rt.card := by omega
          calc R.card
              ≤ 2 * Rt.card := hheavy
            _ ≤ 2 * (2 ^ u * R'.card) := Nat.mul_le_mul_left 2 hrow
            _ = 2 ^ (u + 1) * R'.card := by ring
        · intro a ha b hb
          have hfa : f a = true := (Finset.mem_filter.mp (hR' ha)).2
          simp [Protocol.eval, hfa, hmono a ha b hb]
      · obtain ⟨R', C', u, v, z, hR', hC', huv, hrow, hcol, hmono⟩ := ihl Rf C
        refine ⟨R', C', u + 1, v, z, ?_, hC', ?_, ?_, hcol, ?_⟩
        · intro a ha
          exact (Finset.mem_filter.mp (hR' ha)).1
        · simp only [Protocol.cost]
          omega
        · have hheavy : R.card ≤ 2 * Rf.card := by omega
          calc R.card
              ≤ 2 * Rf.card := hheavy
            _ ≤ 2 * (2 ^ u * R'.card) := Nat.mul_le_mul_left 2 hrow
            _ = 2 ^ (u + 1) * R'.card := by ring
        · intro a ha b hb
          have hfa : ¬ f a = true := (Finset.mem_filter.mp (hR' ha)).2
          simp [Protocol.eval, hfa, hmono a ha b hb]
  | bNode f l r ihl ihr =>
      set Ct : Finset B := C.filter (fun y => f y = true) with hCt
      set Cf : Finset B := C.filter (fun y => ¬ f y = true) with hCf
      have hcardsum : Ct.card + Cf.card = C.card := by
        rw [hCt, hCf]
        exact Finset.card_filter_add_card_filter_not
          (s := C) (p := fun y => f y = true)
      by_cases hhalf : Cf.card ≤ Ct.card
      · obtain ⟨R', C', u, v, z, hR', hC', huv, hrow, hcol, hmono⟩ := ihr R Ct
        refine ⟨R', C', u, v + 1, z, hR', ?_, ?_, hrow, ?_, ?_⟩
        · intro b hb
          exact (Finset.mem_filter.mp (hC' hb)).1
        · simp only [Protocol.cost]
          omega
        · have hheavy : C.card ≤ 2 * Ct.card := by omega
          calc C.card
              ≤ 2 * Ct.card := hheavy
            _ ≤ 2 * (2 ^ v * C'.card) := Nat.mul_le_mul_left 2 hcol
            _ = 2 ^ (v + 1) * C'.card := by ring
        · intro a ha b hb
          have hfb : f b = true := (Finset.mem_filter.mp (hC' hb)).2
          simp [Protocol.eval, hfb, hmono a ha b hb]
      · obtain ⟨R', C', u, v, z, hR', hC', huv, hrow, hcol, hmono⟩ := ihl R Cf
        refine ⟨R', C', u, v + 1, z, hR', ?_, ?_, hrow, ?_, ?_⟩
        · intro b hb
          exact (Finset.mem_filter.mp (hC' hb)).1
        · simp only [Protocol.cost]
          omega
        · have hheavy : C.card ≤ 2 * Cf.card := by omega
          calc C.card
              ≤ 2 * Cf.card := hheavy
            _ ≤ 2 * (2 ^ v * C'.card) := Nat.mul_le_mul_left 2 hcol
            _ = 2 ^ (v + 1) * C'.card := by ring
        · intro a ha b hb
          have hfb : ¬ f b = true := (Finset.mem_filter.mp (hC' hb)).2
          simp [Protocol.eval, hfb, hmono a ha b hb]

/-- Companion: a protocol of cost at most `c` computing a finite game yields a
large monochromatic rectangle with Alice/Bob bit counters summing to `c`. -/
theorem exists_mono_rectangle_of_D_le {A B : Type*} [Fintype A] [Fintype B]
    (g : A → B → Bool) {c : ℕ} (hD : D g ≤ c) :
    ∃ (R : Finset A) (C : Finset B) (u v : ℕ) (z : Bool),
      u + v ≤ c ∧
      Fintype.card A ≤ 2 ^ u * R.card ∧
      Fintype.card B ≤ 2 ^ v * C.card ∧
      ∀ a ∈ R, ∀ b ∈ C, g a b = z := by
  classical
  have hne : (AchievableCosts g).Nonempty :=
    Workspace.UpperBound.AchievableCosts_nonempty g
  have hmem : D g ∈ AchievableCosts g := by
    have := Nat.sInf_mem hne
    simpa [D] using this
  obtain ⟨P, hcost, hcomp⟩ := hmem
  obtain ⟨R, C, u, v, z, _hRsub, _hCsub, huv, hrow, hcol, hmono⟩ :=
    protocol_exists_heavy_rectangle P (Finset.univ : Finset A) (Finset.univ : Finset B)
  refine ⟨R, C, u, v, z, ?_, ?_, ?_, ?_⟩
  · rw [hcost] at huv
    exact le_trans huv hD
  · simpa [Finset.card_univ] using hrow
  · simpa [Finset.card_univ] using hcol
  · intro a ha b hb
    rw [← hcomp a b]
    exact hmono a ha b hb

/-- Companion: chosen-coordinate version of `stage1_rect_bound`, with the
coordinate tuple supplied by an arbitrary injection `e`. This is the shared
rectangle-counting core for initial segments and dense chosen-coordinate
subfamilies. -/
theorem stage1_rect_bound_at (d : ℕ) (hbal : Params.t1 d ≤ Params.q1 d + 5)
    {u : ℕ} {e : Fin u → Fin (Params.q1 d + 5)} (he : Function.Injective e)
    {A : Finset (Fin u × Fin 1)} {B : Finset (C1 d)} {z : Bool}
    (hmono : ∀ p ∈ A, ∀ j ∈ B, HlocalAt d (S1fam d) e p j = z)
    {s : ℕ} (hs1 : s ≤ A.card) (hst : s ≤ Params.t1 d) :
    (B.card : ℝ) ≤
      (1 + epsQT (Params.q1 d + 5) (Params.t1 d)) / (2 : ℝ) ^ s * (L1 d : ℝ) := by
  classical
  obtain ⟨A0, hA0sub, hA0card⟩ := Finset.exists_subset_card_eq hs1
  let coord : Fin u × Fin 1 → Fin (Params.q1 d + 5) := fun p => e p.1
  set J : Finset (Fin (Params.q1 d + 5)) := A0.image coord with hJ
  have hcoord_inj : Set.InjOn coord A0 := by
    intro p _hp q _hq hpq
    apply Prod.ext
    · exact he (by simpa [coord] using hpq)
    · exact Subsingleton.elim _ _
  have hJcard : J.card = s := by
    rw [hJ, Finset.card_image_of_injOn hcoord_inj, hA0card]
  let pat : Fin (Params.q1 d + 5) → Fin 2 := fun _ => if z then 0 else 1
  set F : Finset (C1 d) :=
    Finset.univ.filter (fun j : C1 d => ∀ γ ∈ J, S1fam d j γ = pat γ) with hF
  have hBsub : B ⊆ F := by
    intro j hj
    rw [hF, Finset.mem_filter]
    refine ⟨Finset.mem_univ j, ?_⟩
    intro γ hγ
    rw [hJ, Finset.mem_image] at hγ
    obtain ⟨p, hpA0, hpγ⟩ := hγ
    have hpA : p ∈ A := hA0sub hpA0
    have hval := hmono p hpA j hj
    have hval' : M0 p.2 (S1fam d j (coord p)) = z := by
      simpa [HlocalAt, relaxedInterlace, coord] using hval
    have hpat := stage1_fin2_of_M0 p.2 (S1fam d j (coord p)) z hval'
    rw [← hpγ]
    exact hpat
  have hFcard : (B.card : ℝ) ≤ (F.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hBsub
  have hS := S1fam_balanced d hbal
  have hJt : J.card ≤ Params.t1 d := by
    rw [hJcard]
    exact hst
  have hbalJ := hS.2 J hJt pat
  rw [← hF] at hbalJ
  simp only [Fintype.card_fin] at hbalJ
  rw [hJcard] at hbalJ
  have hLR : (0 : ℝ) < (L1 d : ℝ) := by
    exact_mod_cast (L1_pos d hbal)
  have hdiv :
      (F.card : ℝ) / (L1 d : ℝ) ≤
        (1 + epsQT (Params.q1 d + 5) (Params.t1 d)) / (2 : ℝ) ^ s := by
    have hupper := (abs_le.mp hbalJ).2
    have hsum :
        (1 : ℝ) / (2 : ℝ) ^ s
          + epsQT (Params.q1 d + 5) (Params.t1 d) / (2 : ℝ) ^ s
        = (1 + epsQT (Params.q1 d + 5) (Params.t1 d)) / (2 : ℝ) ^ s := by
      ring
    linarith
  have hFbound :
      (F.card : ℝ) ≤
        (1 + epsQT (Params.q1 d + 5) (Params.t1 d)) / (2 : ℝ) ^ s
          * (L1 d : ℝ) := by
    exact (div_le_iff₀ hLR).mp hdiv
  exact le_trans hFcard hFbound

/-- Companion: paper `claim:stage1-rect-bound`, the balanced-family upper
fiber bound for monochromatic rectangles in a local Stage-1 game. -/
theorem stage1_rect_bound (d : ℕ) (hbal : Params.t1 d ≤ Params.q1 d + 5)
    {r : ℕ} (hr : r ≤ Params.q1 d + 5)
    {A : Finset (Fin r × Fin 1)} {B : Finset (C1 d)} {z : Bool}
    (hmono : ∀ p ∈ A, ∀ j ∈ B, Hlocal d (S1fam d) r hr p j = z)
    {s : ℕ} (hs1 : s ≤ A.card) (hst : s ≤ Params.t1 d) :
    (B.card : ℝ) ≤
      (1 + epsQT (Params.q1 d + 5) (Params.t1 d)) / (2 : ℝ) ^ s * (L1 d : ℝ) := by
  classical
  exact stage1_rect_bound_at d hbal (e := Fin.castLE hr) (Fin.castLE_injective hr)
    (by simpa [Hlocal_eq_HlocalAt] using hmono) hs1 hst

/-- Companion: the column lower bound from a heavy path is incompatible with
the balanced rectangle upper bound when `ε < 1`. -/
private theorem stage1_no_heavy_column (d : ℕ)
    (hbal : Params.t1 d ≤ Params.q1 d + 5)
    {v : ℕ} {C : Finset (C1 d)}
    (hcol : L1 d ≤ 2 ^ v * C.card)
    (hrect :
      (C.card : ℝ) ≤
        (1 + epsQT (Params.q1 d + 5) (Params.t1 d)) / (2 : ℝ) ^ (v + 1)
          * (L1 d : ℝ)) : False := by
  have hq : 0 < Params.q1 d + 5 := by omega
  have hεlt : epsQT (Params.q1 d + 5) (Params.t1 d) < 1 :=
    epsQT_lt_one hq (Params.t1_pos d)
  have hLR : (0 : ℝ) < (L1 d : ℝ) := by
    exact_mod_cast (L1_pos d hbal)
  have hcolR : (L1 d : ℝ) ≤ (2 : ℝ) ^ v * (C.card : ℝ) := by
    exact_mod_cast hcol
  have hchain :
      (L1 d : ℝ) ≤
        ((1 + epsQT (Params.q1 d + 5) (Params.t1 d)) / 2) * (L1 d : ℝ) := by
    calc (L1 d : ℝ)
        ≤ (2 : ℝ) ^ v * (C.card : ℝ) := hcolR
      _ ≤ (2 : ℝ) ^ v *
          ((1 + epsQT (Params.q1 d + 5) (Params.t1 d)) / (2 : ℝ) ^ (v + 1)
            * (L1 d : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hrect (by positivity)
      _ = ((1 + epsQT (Params.q1 d + 5) (Params.t1 d)) / 2) * (L1 d : ℝ) := by
            rw [pow_succ]
            field_simp [show (2 : ℝ) ^ v ≠ 0 by positivity]
  have hlt :
      ((1 + epsQT (Params.q1 d + 5) (Params.t1 d)) / 2) * (L1 d : ℝ)
        < (L1 d : ℝ) := by
    have hfactor : (1 + epsQT (Params.q1 d + 5) (Params.t1 d)) / 2 < (1 : ℝ) := by
      linarith
    nlinarith
  exact (not_lt_of_ge hchain) hlt

/-- Companion: capacity row arithmetic, from `2^a` initial rows and a heavy
path with `u + v ≤ a`. -/
private theorem stage1_cap_rows_large {a u v n : ℕ}
    (hrow : 2 ^ a ≤ 2 ^ u * n) (huv : u + v ≤ a) :
    v + 1 ≤ n := by
  have hu : u ≤ a := by omega
  have hpow : 2 ^ a = 2 ^ u * 2 ^ (a - u) := by
    rw [← pow_add]
    congr 1
    omega
  have hpowle : 2 ^ (a - u) ≤ n := by
    have hrow' : 2 ^ u * 2 ^ (a - u) ≤ 2 ^ u * n := by
      rwa [← hpow]
    exact Nat.le_of_mul_le_mul_left hrow' (Nat.two_pow_pos u)
  have hvpow : v + 1 ≤ 2 ^ (a - u) := by
    have hk : (a - u) + 1 ≤ 2 ^ (a - u) :=
      Nat.succ_le_of_lt Nat.lt_two_pow_self
    omega
  exact le_trans hvpow hpowle

/-- Companion: overload row arithmetic, from `2^a + 1` initial rows and a
heavy path with `u + v ≤ a + 1`. -/
private theorem stage1_over_rows_large {a u v n : ℕ}
    (hrow : 2 ^ a + 1 ≤ 2 ^ u * n) (huv : u + v ≤ a + 1) :
    v + 1 ≤ n := by
  have hu : u ≤ a + 1 := by omega
  by_cases hua : u ≤ a
  · have hpow : 2 ^ a = 2 ^ u * 2 ^ (a - u) := by
      rw [← pow_add]
      congr 1
      omega
    have hltmul : 2 ^ u * 2 ^ (a - u) < 2 ^ u * n := by
      rw [← hpow]
      exact lt_of_lt_of_le (Nat.lt_succ_self _) hrow
    have hlt : 2 ^ (a - u) < n :=
      Nat.lt_of_mul_lt_mul_left hltmul
    have hsucc : 2 ^ (a - u) + 1 ≤ n := Nat.succ_le_of_lt hlt
    have hk : (a - u) + 1 ≤ 2 ^ (a - u) :=
      Nat.succ_le_of_lt Nat.lt_two_pow_self
    omega
  · have hu_eq : u = a + 1 := by omega
    have hv0 : v = 0 := by omega
    have hnpos : 0 < n := by
      by_contra hn
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      rw [hn0, mul_zero] at hrow
      exact (Nat.not_succ_le_zero (2 ^ a)) hrow
    omega

/-- Companion: capacity upper bound for the Stage-1 local threshold game. -/
theorem stage1_cap_upper (d : ℕ) (hd : 2 ≤ d) :
    D (Hcap d) ≤ Params.a d + 1 := by
  classical
  refine comp_le_of_row_types_succ (Hcap d) (Params.a d)
    (fun p : Fin (Params.q1 d + 2) × Fin 1 => Fin.cast (q1_add_two_eq hd) p.1) ?_
  intro x₁ x₂ hτ
  have hrow : x₁.1 = x₂.1 := by
    apply Fin.ext
    have hv := congrArg (fun x : Fin (2 ^ Params.a d) => x.val) hτ
    simpa using hv
  have hx : x₁ = x₂ := by
    exact Prod.ext hrow (Subsingleton.elim _ _)
  rw [hx]

/-- Companion: capacity lower bound for the Stage-1 local threshold game. -/
theorem stage1_cap_lower (d : ℕ) (hd : 2 ≤ d)
    (hbal : Params.t1 d ≤ Params.q1 d + 5)
    (hta : Params.a d + 2 ≤ Params.t1 d) :
    Params.a d + 1 ≤ D (Hcap d) := by
  classical
  by_contra hnot
  have hDle : D (Hcap d) ≤ Params.a d := by omega
  obtain ⟨R, C, u, v, z, huv, hrow, hcol, hmono⟩ :=
    exists_mono_rectangle_of_D_le (Hcap d) hDle
  have hrowNat : Params.q1 d + 2 ≤ 2 ^ u * R.card := by
    simpa [Fintype.card_prod, Fintype.card_fin] using hrow
  have hrowPow : 2 ^ Params.a d ≤ 2 ^ u * R.card := by
    calc
      2 ^ Params.a d = Params.q1 d + 2 := Params.two_pow_a hd
      _ ≤ 2 ^ u * R.card := hrowNat
  have hRlarge : v + 1 ≤ R.card :=
    stage1_cap_rows_large (a := Params.a d) hrowPow huv
  have hst : v + 1 ≤ Params.t1 d := by
    omega
  have hmonoLocal :
      ∀ p ∈ R, ∀ j ∈ C,
        Hlocal d (S1fam d) (Params.q1 d + 2) (by omega) p j = z := by
    intro p hp j hj
    simpa [Hcap] using hmono p hp j hj
  have hrect := stage1_rect_bound d hbal (r := Params.q1 d + 2) (hr := by omega)
    (A := R) (B := C) (z := z) hmonoLocal (s := v + 1) hRlarge hst
  have hcolNat : L1 d ≤ 2 ^ v * C.card := by
    simpa [C1, Fintype.card_fin] using hcol
  exact stage1_no_heavy_column d hbal hcolNat hrect

/-- Companion: overload upper bound for the Stage-1 local threshold game. -/
theorem stage1_over_upper (d : ℕ) (hd : 2 ≤ d) :
    D (Hover d) ≤ Params.a d + 2 := by
  classical
  have hle : Params.q1 d + 3 ≤ 2 ^ (Params.a d + 1) := by
    have h := Params.two_pow_a hd
    rw [pow_succ]
    omega
  have hmain : D (Hover d) ≤ (Params.a d + 1) + 1 := by
    refine comp_le_of_row_types_succ (Hover d) (Params.a d + 1)
      (fun p : Fin (Params.q1 d + 3) × Fin 1 => Fin.castLE hle p.1) ?_
    intro x₁ x₂ hτ
    have hrow : x₁.1 = x₂.1 := by
      apply Fin.ext
      have hv := congrArg (fun x : Fin (2 ^ (Params.a d + 1)) => x.val) hτ
      simpa using hv
    have hx : x₁ = x₂ := by
      exact Prod.ext hrow (Subsingleton.elim _ _)
    rw [hx]
  omega

/-- Companion: overload lower bound for the Stage-1 local threshold game. -/
theorem stage1_over_lower (d : ℕ) (hd : 2 ≤ d)
    (hbal : Params.t1 d ≤ Params.q1 d + 5)
    (hta : Params.a d + 2 ≤ Params.t1 d) :
    Params.a d + 2 ≤ D (Hover d) := by
  classical
  by_contra hnot
  have hDle : D (Hover d) ≤ Params.a d + 1 := by omega
  obtain ⟨R, C, u, v, z, huv, hrow, hcol, hmono⟩ :=
    exists_mono_rectangle_of_D_le (Hover d) hDle
  have hrowNat : Params.q1 d + 3 ≤ 2 ^ u * R.card := by
    simpa [Fintype.card_prod, Fintype.card_fin] using hrow
  have hrowPow : 2 ^ Params.a d + 1 ≤ 2 ^ u * R.card := by
    calc
      2 ^ Params.a d + 1 = Params.q1 d + 3 := (q1_add_three_eq hd).symm
      _ ≤ 2 ^ u * R.card := hrowNat
  have hRlarge : v + 1 ≤ R.card :=
    stage1_over_rows_large (a := Params.a d) hrowPow huv
  have hst : v + 1 ≤ Params.t1 d := by
    omega
  have hmonoLocal :
      ∀ p ∈ R, ∀ j ∈ C,
        Hlocal d (S1fam d) (Params.q1 d + 3) (by omega) p j = z := by
    intro p hp j hj
    simpa [Hover] using hmono p hp j hj
  have hrect := stage1_rect_bound d hbal (r := Params.q1 d + 3) (hr := by omega)
    (A := R) (B := C) (z := z) hmonoLocal (s := v + 1) hRlarge hst
  have hcolNat : L1 d ≤ 2 ^ v * C.card := by
    simpa [C1, Fintype.card_fin] using hcol
  exact stage1_no_heavy_column d hbal hcolNat hrect

-- CLAIM-BEGIN lem:stage1-threshold
/-- Paper `lem:stage1-threshold` (Stage-1 threshold, App C.2): the EXACT local
threshold equalities `comp 𝓗_{2^a}(S₁) = a+1` and `comp 𝓗_{2^a+1}(S₁) = a+2`,
spelled underflow-free: the capacity game is `Hcap` (`r = q₁+2`, the paper's
`2^a` under `2 ≤ d` via `q1_add_two_eq`) and the overload game is `Hover`
(`r = q₁+3`, the paper's `2^a+1` via `q1_add_three_eq`). BOTH directions of
BOTH equalities are native: upper bounds by the row-identification protocol
(`comp_le_of_row_types_succ`), lower bounds by the heavy-path +
balanced-rectangle counting argument (paper `claim:stage1-rect-bound`), NOT
by the robust-seed engine. Large-`d` gates are use-site hypotheses delivered
downstream by `lem:large-d-checklist`: `hbal` exposes the S₁ balancedness
(`S1fam_balanced`), `hta` is the paper's eq:stage1-t-large `a+2 ≤ t₁`. -/
theorem stage1_threshold (d : ℕ) (hd : 2 ≤ d)
    (hbal : Params.t1 d ≤ Params.q1 d + 5)
    (hta : Params.a d + 2 ≤ Params.t1 d) :
    D (Hcap d) = Params.a d + 1 ∧ D (Hover d) = Params.a d + 2 :=
-- CLAIM-END lem:stage1-threshold
  by
  exact ⟨le_antisymm (stage1_cap_upper d hd) (stage1_cap_lower d hd hbal hta),
    le_antisymm (stage1_over_upper d hd) (stage1_over_lower d hd hbal hta)⟩

/-! ## Stage-0 seed column-loss resilience (`lem:M0-column-loss-resilient`)

The degenerate base case of the odd-copy engine. The seed `M₀ = [1 0]` has
`D M₀ = 1`, so the `Λ`-rung ladder `odd_copy_seed_rungs` (which needs `D f ≥ 2`)
does not apply; instead the resilience clauses reduce to ONE-COPY nontriviality.
The proof below handles this seed directly and is then consumed by the Stage-1
residual-hardness theorem. -/

open Workspace.Types.Interlace

/-- Companion: the seed `M₀ = [1 0]` costs at most one bit — it is a single-row
game (Bob announces the value), via the unit-row protocol transported along
`Unit ≃ Fin 1`. -/
theorem D_M0_le_one : D M0 ≤ 1 := by
  have hunit : D (fun (_ : Unit) (y : Fin 2) => M0 0 y) ≤ 1 :=
    D_le_one_of_unit_row (fun y => M0 0 y)
  have heq : D (fun (_ : Unit) (y : Fin 2) => M0 0 y) = D M0 := by
    have h := D_equiv_invariance M0 (Equiv.ofUnique (α := Unit) (β := Fin 1))
      (Equiv.refl (Fin 2))
    convert h using 3
  rw [← heq]; exact hunit

/-- Companion: a two-party game taking two distinct values has `D ≥ 1` — no
cost-`0` (leaf) protocol computes a nonconstant game. -/
theorem one_le_D_of_two_values {A B : Type*} [Fintype A] [Fintype B]
    (g : A → B → Bool) {a₁ a₂ : A} {b₁ b₂ : B} (hne : g a₁ b₁ ≠ g a₂ b₂) :
    1 ≤ D g := by
  by_contra h
  have h0 : D g = 0 := by omega
  have hne' : (AchievableCosts g).Nonempty :=
    Workspace.UpperBound.AchievableCosts_nonempty g
  have hmem : (0 : ℕ) ∈ AchievableCosts g := by
    have := Nat.sInf_mem hne'
    rw [← h0]; simpa [D] using this
  obtain ⟨P, hcost, hcomp⟩ := hmem
  cases P with
  | leaf z =>
      have h1 := hcomp a₁ b₁
      have h2 := hcomp a₂ b₂
      simp only [Protocol.eval] at h1 h2
      exact hne (by rw [← h1, ← h2])
  | aNode a l r => simp [Protocol.cost] at hcost
  | bNode b l r => simp [Protocol.cost] at hcost

/-- Companion: `M₀` is nonconstant, hence `1 ≤ D M₀`. -/
theorem one_le_D_M0 : 1 ≤ D M0 :=
  one_le_D_of_two_values M0 (a₁ := 0) (a₂ := 0) (b₁ := 0) (b₂ := 1) (by decide)

/-- Companion: `D M₀ = 1` (the ledger's stated seed fact; `M₀` is a nonconstant
one-row game). -/
theorem D_M0_eq_one : D M0 = 1 := le_antisymm D_M0_le_one one_le_D_M0

/-- Companion (one-copy seed nontriviality): at a column density `y > 1/2` the
one-copy family of `M₀` is nontrivial (`comp ≥ 1`). Reason: the column threshold
`⌈2y⌉ ≥ 2` forces every member to keep BOTH columns of `Fin 1 → Fin 2`, so its
subgame reads both `M₀ 0 0 = true` and `M₀ 0 1 = false` — nonconstant. This is
the exact one-copy fact both resilience clauses consume (clause (i) at the seed
density, clause (ii) `k = 0` at each `y_c`). -/
theorem one_le_Dfamily_M0_of_half_lt {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hy : 1 / 2 < y) (hy1 : y ≤ 1) :
    1 ≤ Dfamily (interlaceFun M0 1) (bracketGE (Fin 1) (Fin 2) 1 x y) := by
  classical
  set S : Set ℕ := { d : ℕ | ∃ RC ∈ bracketGE (Fin 1) (Fin 2) 1 x y,
      d = D (subgame (interlaceFun M0 1) RC.1 RC.2) } with hS
  have hXcard : 1 ≤ Fintype.card (Fin 1) := by simp
  have hbne : (bracketGE (Fin 1) (Fin 2) 1 x y).Nonempty :=
    bracketGE.nonempty 1 x y hx1 hy1 hXcard
  have hSne : S.Nonempty := by
    obtain ⟨RC, hRC⟩ := hbne; exact ⟨_, RC, hRC, rfl⟩
  have hmemge : ∀ n ∈ S, 1 ≤ n := by
    rintro n ⟨⟨R, C⟩, ⟨hRow, hCol⟩, rfl⟩
    have hcolth : (2 : ℕ) ≤ C.card := by
      have hth : (2 : ℕ) ≤ ⌈((Fintype.card (Fin 2) : ℝ) ^ 1) * y⌉₊ := by
        have hgt : ((1 : ℕ) : ℝ) < ((Fintype.card (Fin 2) : ℝ) ^ 1) * y := by
          simp only [Fintype.card_fin, pow_one, Nat.cast_ofNat, Nat.cast_one]; linarith
        have hlt := Nat.lt_ceil.mpr hgt; omega
      exact le_trans hth hCol
    have hCuniv : C = Finset.univ := by
      have hle : C.card ≤ (Finset.univ : Finset (Fin 1 → Fin 2)).card :=
        Finset.card_le_univ C
      have hcard2 : (Finset.univ : Finset (Fin 1 → Fin 2)).card = 2 := by decide
      have hceq : C.card = (Finset.univ : Finset (Fin 1 → Fin 2)).card := by omega
      exact Finset.eq_univ_of_card C hceq
    have hrowth : (1 : ℕ) ≤ ⌈(Fintype.card (Fin 1) : ℝ) * x⌉₊ := by
      have hpos : (0 : ℝ) < (Fintype.card (Fin 1) : ℝ) * x := by
        simp only [Fintype.card_fin, Nat.cast_one]; linarith
      exact Nat.one_le_ceil_iff.mpr hpos
    have hfib : 1 ≤ (R.filter (fun p => p.1 = (0 : Fin 1))).card :=
      le_trans hrowth (hRow 0 (Finset.mem_univ 0))
    obtain ⟨pr, hpr⟩ :=
      Finset.card_pos.mp (by omega : 0 < (R.filter (fun p => p.1 = (0 : Fin 1))).card)
    rw [Finset.mem_filter] at hpr
    have hprR : pr ∈ R := hpr.1
    have hpr00 : pr = ((0 : Fin 1), (0 : Fin 1)) := by
      apply Prod.ext <;> exact Subsingleton.elim _ _
    have hc0 : (fun _ : Fin 1 => (0 : Fin 2)) ∈ C := by rw [hCuniv]; exact Finset.mem_univ _
    have hc1 : (fun _ : Fin 1 => (1 : Fin 2)) ∈ C := by rw [hCuniv]; exact Finset.mem_univ _
    refine one_le_D_of_two_values (subgame (interlaceFun M0 1) R C)
      (a₁ := ⟨pr, hprR⟩) (a₂ := ⟨pr, hprR⟩) (b₁ := ⟨_, hc0⟩) (b₂ := ⟨_, hc1⟩) ?_
    subst hpr00; simp [subgame, interlaceFun, M0]
  have hEq : Dfamily (interlaceFun M0 1) (bracketGE (Fin 1) (Fin 2) 1 x y) = sInf S := rfl
  rw [hEq, Nat.one_le_iff_ne_zero]
  intro h0
  rcases (Nat.sInf_eq_zero.mp h0) with hin | hemp
  · exact absurd (hmemge 0 hin) (by norm_num)
  · rw [hemp] at hSne; exact absurd hSne (by simp)

/-- Companion (density upper bound): a one-copy loss density is `≤ 1` when its
base `(h·2^{−c})/(1+ε)` lies in `[0,1]` (the `1/t`-th root is monotone). -/
theorem yLoss_le_one {ε : ℝ} {t : ℕ} {h : ℝ} {c : ℕ}
    (hbase0 : 0 ≤ (h * (2 : ℝ) ^ (-(c : ℝ))) / (1 + ε))
    (hbase1 : (h * (2 : ℝ) ^ (-(c : ℝ))) / (1 + ε) ≤ 1) :
    yLoss ε t h c ≤ 1 := by
  unfold yLoss
  calc ((h * (2 : ℝ) ^ (-(c : ℝ))) / (1 + ε)) ^ (1 / (t : ℝ))
      ≤ (1 : ℝ) ^ (1 / (t : ℝ)) := Real.rpow_le_rpow hbase0 hbase1 (by positivity)
    _ = 1 := Real.one_rpow _

/-- Companion (density lower bound, the load-bearing large-`t` fact): the one-copy
loss density exceeds `1/2` whenever its base exceeds `2^{−t}`. Since
`(1/2) = (2^{−t})^{1/t}` and the `1/t`-th root is strictly monotone in the base,
`y_c > 1/2`. At the Stage-1 scale `t = 2^T` is astronomically large, so this holds
with enormous slack for every `c` in the consumed range. -/
theorem half_lt_yLoss {ε : ℝ} {t : ℕ} {h : ℝ} {c : ℕ} (ht : 0 < t)
    (hbase : (2 : ℝ) ^ (-(t : ℝ)) < (h * (2 : ℝ) ^ (-(c : ℝ))) / (1 + ε)) :
    1 / 2 < yLoss ε t h c := by
  unfold yLoss
  set w : ℝ := (h * (2 : ℝ) ^ (-(c : ℝ))) / (1 + ε) with hw
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hbasepos : (0 : ℝ) < (2 : ℝ) ^ (-(t : ℝ)) := by positivity
  have hhalf : ((2 : ℝ) ^ (-(t : ℝ))) ^ (1 / (t : ℝ)) = (1 : ℝ) / 2 := by
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    have hmm : (-(t : ℝ)) * (1 / (t : ℝ)) = -1 := by field_simp
    rw [hmm, Real.rpow_neg_one]; norm_num
  have hmono : ((2 : ℝ) ^ (-(t : ℝ))) ^ (1 / (t : ℝ)) < w ^ (1 / (t : ℝ)) :=
    Real.rpow_lt_rpow (le_of_lt hbasepos) hbase (by positivity)
  rw [hhalf] at hmono; exact hmono

-- CLAIM-BEGIN lem:M0-column-loss-resilient
/-- **`lem:M0-column-loss-resilient`** (an internal lemma without a separate
paper label). The seed `(M₀, b)` is `(2^Q, 2^T, h)`-
column-loss resilient (`NPCC.IsColumnLossResilient`) whenever the row density
`2^{−b} ∈ (0,1]` (i.e. `0 ≤ b`) and every consumed one-copy loss density lies in
`(1/2, 1]`: at the clause-(i) argument `c = Q + D M₀` and, for clause (ii)
`k = 0`, at every `c ≤ T`. These two density gates are exactly the numeric facts
a `LargeD` wrapper supplies (via `half_lt_yLoss` / `yLoss_le_one`): at the
Stage-1 scale `t = 2^T` the `1/t`-th root pins each `y_c` above `1/2` with vast
slack.

Mathematics (`D M₀ = 1`, so the `Λ`-rung engine `odd_copy_seed_rungs` — which
needs `D f ≥ 2` — does NOT apply; the degenerate base case). Clause (i) is the
one-copy nontriviality at the seed density. Clause (ii) ranges `k ≤ D M₀ = 1`:
`k = 1` gives `D M₀ − 1 = 0 ≤ Λ` (trivial); `k = 0` needs
`LambdaGE M₀ 1 (2^{−b}) (y_c) ≥ 1` for all `c ≤ T`, and `Λ = min` bottoms out at
the same one-copy nontriviality `comp(y_c) ≥ 1` (`one_le_Dfamily_M0_of_half_lt`),
the other two rungs being `1+·` and `2+·`. -/
theorem M0_column_loss_resilient
    (b ε : ℝ) (Q T : ℕ) (h : ℝ)
    (hb : 0 ≤ b)
    (hyi_lo : 1 / 2 < yLoss ε (2 ^ T) h (Q + D M0))
    (hyi_hi : yLoss ε (2 ^ T) h (Q + D M0) ≤ 1)
    (hyii_lo : ∀ c ≤ T, 1 / 2 < yLoss ε (2 ^ T) h c)
    (hyii_hi : ∀ c ≤ T, yLoss ε (2 ^ T) h c ≤ 1) :
    IsColumnLossResilient M0 b ε Q T h := by
-- CLAIM-END lem:M0-column-loss-resilient
  have hx0 : (0 : ℝ) < (2 : ℝ) ^ (-b) := by positivity
  have hx1 : (2 : ℝ) ^ (-b) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  constructor
  · -- clause (i): one-copy nontriviality at the seed density
    exact one_le_Dfamily_M0_of_half_lt hx0 hx1 hyi_lo hyi_hi
  · -- clause (ii)
    intro k hk c hc
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- k = 0 : D M₀ − 0 = 1 ≤ Λ, bottoming out at one-copy nontriviality
      subst hk0
      have hcT : c ≤ T := by omega
      have hnt : 1 ≤ Dfamily (interlaceFun M0 1)
          (bracketGE (Fin 1) (Fin 2) 1 ((2 : ℝ) ^ (-b)) (yLoss ε (2 ^ T) h c)) :=
        one_le_Dfamily_M0_of_half_lt hx0 hx1 (hyii_lo c hcT) (hyii_hi c hcT)
      rw [Nat.sub_zero, D_M0_eq_one]
      unfold LambdaGE
      refine le_min hnt (le_min ?_ ?_) <;> omega
    · -- k ≥ 1 : D M₀ − k = 0
      have hz : D M0 - k = 0 := by rw [D_M0_eq_one]; omega
      rw [hz]; exact Nat.zero_le _

/-- Companion: evaluation for a chosen-coordinate local game. -/
theorem HlocalAt_apply (d : ℕ) {L : ℕ}
    (T : Fin L → Fin (Params.q1 d + 5) → Fin 2)
    {u : ℕ} (e : Fin u → Fin (Params.q1 d + 5))
    (a : Fin u × Fin 1) (j : Fin L) :
    HlocalAt d T e a j = M0 a.2 (T j (e a.1)) := rfl

/-- Companion: the dense subfamily restriction of a local initial-segment
game, with columns transported as a subtype of the selected index set. -/
def HlocalSub (d : ℕ) {L : ℕ} (T : Fin L → Fin (Params.q1 d + 5) → Fin 2)
    (S' : Finset (Fin L)) (r : ℕ) (hr : r ≤ Params.q1 d + 5) :
    (Fin r × Fin 1) → {j // j ∈ S'} → Bool :=
  fun p j => Hlocal d T r hr p j.val

/-- Companion: the dense subfamily restriction of a chosen-coordinate local
game, again transporting columns by subtype rather than re-choosing them. -/
def HlocalAtSub (d : ℕ) {L : ℕ} (T : Fin L → Fin (Params.q1 d + 5) → Fin 2)
    (S' : Finset (Fin L)) {u : ℕ} (e : Fin u → Fin (Params.q1 d + 5)) :
    (Fin u × Fin 1) → {j // j ∈ S'} → Bool :=
  fun p j => HlocalAt d T e p j.val

/-- Companion: the dense initial-segment restriction is the chosen-coordinate
restriction at `Fin.castLE`. -/
theorem HlocalSub_eq_HlocalAtSub (d : ℕ) {L : ℕ}
    (T : Fin L → Fin (Params.q1 d + 5) → Fin 2) (S' : Finset (Fin L))
    (r : ℕ) (hr : r ≤ Params.q1 d + 5) :
    HlocalSub d T S' r hr = HlocalAtSub d T S' (Fin.castLE hr) := rfl

/-- Companion: the dense column lower bound from a heavy path contradicts the
generic rectangle bound under the strict real-density gate. -/
private theorem stage1_dense_no_heavy_column (d : ℕ)
    (hbal : Params.t1 d ≤ Params.q1 d + 5)
    {ρ : ℝ} (hρ : ρ < (1 - epsQT (Params.q1 d + 5) (Params.t1 d)) / 2)
    {S' : Finset (C1 d)} (hS' : (1 - ρ) * (L1 d : ℝ) ≤ (S'.card : ℝ))
    {v n : ℕ} (hcol : S'.card ≤ 2 ^ v * n)
    (hrect : (n : ℝ) ≤
      (1 + epsQT (Params.q1 d + 5) (Params.t1 d)) / (2 : ℝ) ^ (v + 1)
        * (L1 d : ℝ)) : False := by
  have hLR : (0 : ℝ) < (L1 d : ℝ) := by
    exact_mod_cast (L1_pos d hbal)
  have hcolR : (S'.card : ℝ) ≤ (2 : ℝ) ^ v * (n : ℝ) := by
    exact_mod_cast hcol
  have hchain :
      (1 - ρ) * (L1 d : ℝ) ≤
        ((1 + epsQT (Params.q1 d + 5) (Params.t1 d)) / 2) * (L1 d : ℝ) := by
    calc (1 - ρ) * (L1 d : ℝ)
        ≤ (S'.card : ℝ) := hS'
      _ ≤ (2 : ℝ) ^ v * (n : ℝ) := hcolR
      _ ≤ (2 : ℝ) ^ v *
          ((1 + epsQT (Params.q1 d + 5) (Params.t1 d)) / (2 : ℝ) ^ (v + 1)
            * (L1 d : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hrect (by positivity)
      _ = ((1 + epsQT (Params.q1 d + 5) (Params.t1 d)) / 2) * (L1 d : ℝ) := by
            rw [pow_succ]
            field_simp [show (2 : ℝ) ^ v ≠ 0 by positivity]
  have hfactor :
      1 - ρ ≤ (1 + epsQT (Params.q1 d + 5) (Params.t1 d)) / 2 :=
    by nlinarith
  linarith

/-- Companion: dense subfamily upper bound for any initial segment with at
most `q₁+2 = 2^a` rows, by the same row-identification protocol. -/
theorem stage1_dense_cap_upper (d : ℕ) (hd : 2 ≤ d) {L : ℕ}
    (T : Fin L → Fin (Params.q1 d + 5) → Fin 2) (S' : Finset (Fin L))
    {r : ℕ} (hr2 : r ≤ Params.q1 d + 2) :
    D (HlocalSub d T S' r (by omega)) ≤ Params.a d + 1 := by
  classical
  have hle : r ≤ 2 ^ Params.a d := by
    have h := Params.two_pow_a hd
    omega
  refine comp_le_of_row_types_succ (HlocalSub d T S' r (by omega)) (Params.a d)
    (fun p : Fin r × Fin 1 => Fin.castLE hle p.1) ?_
  intro x₁ x₂ hτ
  have hrow : x₁.1 = x₂.1 := by
    apply Fin.ext
    have hv := congrArg (fun x : Fin (2 ^ Params.a d) => x.val) hτ
    simpa using hv
  have hx : x₁ = x₂ := by
    exact Prod.ext hrow (Subsingleton.elim _ _)
  rw [hx]

/-- Companion: dense chosen-coordinate lower bound from the heavy-path
rectangle argument, generic in the injected coordinate enumeration. -/
theorem stage1_dense_lower_at (d : ℕ) (hd : 2 ≤ d)
    (hbal : Params.t1 d ≤ Params.q1 d + 5)
    (hta : Params.a d + 2 ≤ Params.t1 d)
    {ρ : ℝ} (hρ : ρ < (1 - epsQT (Params.q1 d + 5) (Params.t1 d)) / 2)
    (S' : Finset (C1 d)) (hS' : (1 - ρ) * (L1 d : ℝ) ≤ (S'.card : ℝ))
    {u : ℕ} (e : Fin u → Fin (Params.q1 d + 5))
    (he : Function.Injective e) (hu : Params.q1 d + 3 ≤ u) :
    Params.a d + 2 ≤ D (HlocalAtSub d (S1fam d) S' e) := by
  classical
  by_contra hnot
  have hDle : D (HlocalAtSub d (S1fam d) S' e) ≤ Params.a d + 1 := by
    omega
  obtain ⟨R, C, u0, v, z, huv, hrow, hcol, hmono⟩ :=
    exists_mono_rectangle_of_D_le (HlocalAtSub d (S1fam d) S' e) hDle
  have hrowNat : u ≤ 2 ^ u0 * R.card := by
    simpa [Fintype.card_prod, Fintype.card_fin] using hrow
  have hrowQ : Params.q1 d + 3 ≤ 2 ^ u0 * R.card :=
    le_trans hu hrowNat
  have hrowPow : 2 ^ Params.a d + 1 ≤ 2 ^ u0 * R.card := by
    calc
      2 ^ Params.a d + 1 = Params.q1 d + 3 := (q1_add_three_eq hd).symm
      _ ≤ 2 ^ u0 * R.card := hrowQ
  have hRlarge : v + 1 ≤ R.card :=
    stage1_over_rows_large (a := Params.a d) hrowPow huv
  have hst : v + 1 ≤ Params.t1 d := by
    omega
  set B' : Finset (C1 d) := C.image Subtype.val with hB'
  have hB'card : B'.card = C.card := by
    rw [hB', Finset.card_image_of_injective C Subtype.val_injective]
  have hmonoAmbient :
      ∀ p ∈ R, ∀ j ∈ B', HlocalAt d (S1fam d) e p j = z := by
    intro p hp j hj
    rw [hB', Finset.mem_image] at hj
    obtain ⟨j', hjC, rfl⟩ := hj
    simpa [HlocalAtSub] using hmono p hp j' hjC
  have hrectB' := stage1_rect_bound_at d hbal (e := e) he
    (A := R) (B := B') (z := z) hmonoAmbient (s := v + 1) hRlarge hst
  have hrect :
      (C.card : ℝ) ≤
        (1 + epsQT (Params.q1 d + 5) (Params.t1 d)) / (2 : ℝ) ^ (v + 1)
          * (L1 d : ℝ) := by
    rwa [hB'card] at hrectB'
  have hcolNat : S'.card ≤ 2 ^ v * C.card := by
    simpa [Fintype.card_coe] using hcol
  exact stage1_dense_no_heavy_column d hbal hρ hS' hcolNat hrect

-- CLAIM-BEGIN cor:stage1-dense-threshold
/-- Paper `cor:stage1-dense-threshold` (App C.2): the Stage-1 threshold
survives on DENSE subfamilies of `S₁`. Data: `S' ⊆ S₁` enters as a `Finset`
of family indices (the game `𝓗_r(S')` is `HlocalSub`, the column-subtype
restriction of `𝓗_r(S₁)` — transport, never re-choice), with REAL density
`|S'| ≥ (1−ρ)|S₁|` (no ℕ truncation) for `ρ ∈ [0,1)` under the STRICT
risk-ledger gate `ρ < (1−ε₁)/2` (never weakened; `ε₁ = ε_{2^a+3,t₁}` is
`epsQT (q₁+5) t₁` via `q1_add_five_eq`). For `0 ≤ ℓ ≤ 4` the paper's
`G'_ℓ := 𝓗_{2^a−1+ℓ}(S')` is spelled underflow-free with row count
`r := q₁+1+ℓ` (`= 2^a−1+ℓ` under `2 ≤ d` by `Params.two_pow_a`); the
conclusions are `ℓ ≤ 1 → comp G'_ℓ ≤ B_cap` and `ℓ ≥ 2 → comp G'_ℓ ≥
B_cap+1` with the budget numeric: `B_cap = a+1` exactly as
`lem:stage1-threshold` pins it (defeq to `Bcap d` of NPCC/Scaffold.lean).
Large-`d` gates `hbal`/`hta` exactly as in `lem:stage1-threshold`. The paper
proof re-runs the rectangle argument on `S'`; here both branches INSTANTIATE
the shared generic machinery (`stage1_dense_cap_upper`;
`stage1_dense_lower_at` at the initial-segment enumeration `Fin.castLE`),
per the ledger's instantiate-don't-copy requirement. -/
theorem stage1_dense_threshold (d : ℕ) (hd : 2 ≤ d)
    (hbal : Params.t1 d ≤ Params.q1 d + 5)
    (hta : Params.a d + 2 ≤ Params.t1 d)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hρ : ρ < (1 - epsQT (Params.q1 d + 5) (Params.t1 d)) / 2)
    (S' : Finset (C1 d)) (hS' : (1 - ρ) * (L1 d : ℝ) ≤ (S'.card : ℝ))
    (ℓ : ℕ) (hℓ : ℓ ≤ 4) :
    (ℓ ≤ 1 →
      D (HlocalSub d (S1fam d) S' (Params.q1 d + 1 + ℓ) (by omega))
        ≤ Params.a d + 1) ∧
    (2 ≤ ℓ →
      Params.a d + 2 ≤
        D (HlocalSub d (S1fam d) S' (Params.q1 d + 1 + ℓ) (by omega))) :=
-- CLAIM-END cor:stage1-dense-threshold
  by
  have _ := hρ0
  have _ := hρ1
  constructor
  · intro hℓ1
    exact stage1_dense_cap_upper d hd (S1fam d) S'
      (r := Params.q1 d + 1 + ℓ) (by omega)
  · intro hℓ2
    have hr : Params.q1 d + 1 + ℓ ≤ Params.q1 d + 5 := by
      omega
    have hinit := stage1_dense_lower_at d hd hbal hta hρ S' hS'
      (Fin.castLE hr) (Fin.castLE_injective hr) (by omega)
    simpa [HlocalSub_eq_HlocalAtSub d (S1fam d) S' (Params.q1 d + 1 + ℓ) hr]
      using hinit

-- CLAIM-BEGIN cor:stage1-chosen-dense-threshold
/-- Paper `cor:stage1-chosen-dense-threshold` (Chosen-coordinate dense
Stage-1 threshold, App C.2) — THE lemma the final NO-case contradiction
fires, also consumed by the Stage-4 gadget lemmas. Same dense data as
`cor:stage1-dense-threshold` (`S'` a `Finset` of `S₁` indices, REAL density
`|S'| ≥ (1−ρ)|S₁|`, `ρ ∈ [0,1)`, STRICT gate `ρ < (1−ε₁)/2`). The chosen
coordinate set `Q ⊆ [2^a+3]` with `|Q| ≥ 2^a+1` enters as an INJECTIVE
enumeration `e : Fin u → Fin (q₁+5)` with `u ≥ q₁+3` (the paper's `2^a+1`
via `q1_add_three_eq`); per the risk ledger the quantification is over EVERY
such `Q` — `e` is arbitrary injective, never just an initial segment — and
the game is `HlocalAtSub`, the extraction of the relaxed interlace to
`Q × Rows(M₀)` over the subfamily columns `S'`. Conclusion:
`comp ≥ B_cap+1 = a+2` (numeric, as `lem:stage1-threshold` pins `B_cap`).
Proof: one instantiation of the generic dense heavy-path lower bound
(`stage1_dense_lower_at`); the paper's trim-to-`Q'`-then-apply route
collapses because the shared rectangle bound (`stage1_rect_bound_at`) is
generic in the enumeration, exactly as the paper's own proof remarks. -/
theorem stage1_chosen_dense_threshold (d : ℕ) (hd : 2 ≤ d)
    (hbal : Params.t1 d ≤ Params.q1 d + 5)
    (hta : Params.a d + 2 ≤ Params.t1 d)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hρ : ρ < (1 - epsQT (Params.q1 d + 5) (Params.t1 d)) / 2)
    (S' : Finset (C1 d)) (hS' : (1 - ρ) * (L1 d : ℝ) ≤ (S'.card : ℝ))
    {u : ℕ} (e : Fin u → Fin (Params.q1 d + 5))
    (he : Function.Injective e) (hu : Params.q1 d + 3 ≤ u) :
    Params.a d + 2 ≤ D (HlocalAtSub d (S1fam d) S' e) :=
-- CLAIM-END cor:stage1-chosen-dense-threshold
  by
  have _ := hρ0
  have _ := hρ1
  exact stage1_dense_lower_at d hd hbal hta hρ S' hS' e he hu


section M1LowColumnStage2

open Workspace.Types.Interlace

private lemma two_zpow_neg_nat_eq_rpow_neg_nat (n : ℕ) :
    (2 : ℝ) ^ (-(n : ℤ)) = (2 : ℝ) ^ (-(n : ℝ)) := by
  have hcast : (((-(n : ℤ) : ℤ) : ℝ) = -(n : ℝ)) := by norm_num
  rw [hcast.symm]
  exact (Real.rpow_intCast (2 : ℝ) (-(n : ℤ))).symm

private lemma two_rpow_neg_add_one (A c : ℕ) :
    (2 : ℝ) ^ (-(((A + c + 1 : ℕ) : ℝ))) =
      (2 : ℝ) ^ (-(A : ℝ)) * (2 : ℝ) ^ (-(c : ℝ)) / 2 := by
  rw [show (2 : ℝ) ^ (-(A : ℝ)) * (2 : ℝ) ^ (-(c : ℝ)) / 2 =
      (2 : ℝ) ^ (-(A : ℝ)) * (2 : ℝ) ^ (-(c : ℝ)) * (2 : ℝ) ^ (-1 : ℝ) by
        rw [Real.rpow_neg_one]; ring]
  rw [(Real.rpow_add (by norm_num : (0 : ℝ) < 2) (-(A : ℝ)) (-(c : ℝ))).symm]
  rw [(Real.rpow_add (by norm_num : (0 : ℝ) < 2) (-(A : ℝ) + -(c : ℝ)) (-1 : ℝ)).symm]
  congr 1
  norm_num
  ring

private lemma stage2_base_lower {A c n : ℕ} {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hlt : A + c + 1 < n) :
    (2 : ℝ) ^ (-(n : ℝ)) <
      (2 : ℝ) ^ (-(A : ℤ)) * (2 : ℝ) ^ (-(c : ℝ)) / (1 + ε) := by
  have hpow : (2 : ℝ) ^ (-(n : ℝ)) < (2 : ℝ) ^ (-(((A + c + 1 : ℕ) : ℝ))) := by
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
    have hltR : (((A + c + 1 : ℕ) : ℝ) < (n : ℝ)) := by exact_mod_cast hlt
    linarith
  have hhalf : (2 : ℝ) ^ (-(((A + c + 1 : ℕ) : ℝ))) =
      (2 : ℝ) ^ (-(A : ℝ)) * (2 : ℝ) ^ (-(c : ℝ)) / 2 :=
    two_rpow_neg_add_one A c
  have hz := two_zpow_neg_nat_eq_rpow_neg_nat A
  have hnumpos : 0 < (2 : ℝ) ^ (-(A : ℝ)) * (2 : ℝ) ^ (-(c : ℝ)) := by positivity
  have hdiv : (2 : ℝ) ^ (-(A : ℝ)) * (2 : ℝ) ^ (-(c : ℝ)) / 2 <
      (2 : ℝ) ^ (-(A : ℝ)) * (2 : ℝ) ^ (-(c : ℝ)) / (1 + ε) := by
    apply div_lt_div_of_pos_left hnumpos (by linarith) (by linarith)
  calc (2 : ℝ) ^ (-(n : ℝ))
      < (2 : ℝ) ^ (-(((A + c + 1 : ℕ) : ℝ))) := hpow
    _ = (2 : ℝ) ^ (-(A : ℝ)) * (2 : ℝ) ^ (-(c : ℝ)) / 2 := hhalf
    _ < (2 : ℝ) ^ (-(A : ℝ)) * (2 : ℝ) ^ (-(c : ℝ)) / (1 + ε) := hdiv
    _ = (2 : ℝ) ^ (-(A : ℤ)) * (2 : ℝ) ^ (-(c : ℝ)) / (1 + ε) := by rw [hz]

private lemma stage2_base_le_one {A c : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε) :
    (2 : ℝ) ^ (-(A : ℤ)) * (2 : ℝ) ^ (-(c : ℝ)) / (1 + ε) ≤ 1 := by
  have hzle : (2 : ℝ) ^ (-(A : ℤ)) ≤ 1 := by
    rw [two_zpow_neg_nat_eq_rpow_neg_nat A]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
    exact neg_nonpos.mpr (Nat.cast_nonneg A)
  have hrle : (2 : ℝ) ^ (-(c : ℝ)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
    exact neg_nonpos.mpr (Nat.cast_nonneg c)
  have hrnon : 0 ≤ (2 : ℝ) ^ (-(c : ℝ)) := le_of_lt (by positivity)
  have hnumle : (2 : ℝ) ^ (-(A : ℤ)) * (2 : ℝ) ^ (-(c : ℝ)) ≤ 1 := by
    calc (2 : ℝ) ^ (-(A : ℤ)) * (2 : ℝ) ^ (-(c : ℝ))
        ≤ 1 * 1 := mul_le_mul hzle hrle hrnon (by norm_num)
      _ = 1 := by ring
  have hnum_non : 0 ≤ (2 : ℝ) ^ (-(A : ℤ)) * (2 : ℝ) ^ (-(c : ℝ)) := by positivity
  calc (2 : ℝ) ^ (-(A : ℤ)) * (2 : ℝ) ^ (-(c : ℝ)) / (1 + ε)
      ≤ (2 : ℝ) ^ (-(A : ℤ)) * (2 : ℝ) ^ (-(c : ℝ)) / 1 := by
        apply div_le_div_of_nonneg_left hnum_non (by norm_num) (by linarith)
    _ ≤ 1 := by simpa using hnumle

private lemma stage2_bridge_base {A c : ℕ} {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    (2 : ℝ) ^ (-(((A + c + 1 : ℕ) : ℝ))) ≤
      (2 : ℝ) ^ (-(A : ℤ)) * (2 : ℝ) ^ (-(c : ℝ)) / (1 + ε) := by
  have hhalf : (2 : ℝ) ^ (-(((A + c + 1 : ℕ) : ℝ))) =
      (2 : ℝ) ^ (-(A : ℝ)) * (2 : ℝ) ^ (-(c : ℝ)) / 2 :=
    two_rpow_neg_add_one A c
  have hz := two_zpow_neg_nat_eq_rpow_neg_nat A
  have hnumpos : 0 < (2 : ℝ) ^ (-(A : ℝ)) * (2 : ℝ) ^ (-(c : ℝ)) := by positivity
  have hdiv : (2 : ℝ) ^ (-(A : ℝ)) * (2 : ℝ) ^ (-(c : ℝ)) / 2 <
      (2 : ℝ) ^ (-(A : ℝ)) * (2 : ℝ) ^ (-(c : ℝ)) / (1 + ε) := by
    apply div_lt_div_of_pos_left hnumpos (by linarith) (by linarith)
  calc (2 : ℝ) ^ (-(((A + c + 1 : ℕ) : ℝ)))
      = (2 : ℝ) ^ (-(A : ℝ)) * (2 : ℝ) ^ (-(c : ℝ)) / 2 := hhalf
    _ ≤ (2 : ℝ) ^ (-(A : ℝ)) * (2 : ℝ) ^ (-(c : ℝ)) / (1 + ε) := le_of_lt hdiv
    _ = (2 : ℝ) ^ (-(A : ℤ)) * (2 : ℝ) ^ (-(c : ℝ)) / (1 + ε) := by rw [hz]

private lemma pow_two_log_eq_of_pow2 {n : ℕ} (h : ∃ k, n = 2 ^ k) :
    n = 2 ^ Nat.log 2 n := by
  obtain ⟨k, rfl⟩ := h
  rw [log_two_pow]

private lemma dfamily_singleton_local {A B : Type*} (f : A → B → Bool)
    (RC : Finset A × Finset B) :
    Dfamily f {RC} = D (subgame f RC.1 RC.2) := by
  unfold Dfamily
  have hset :
      { d : ℕ | ∃ RC' ∈ ({RC} : Set (Finset A × Finset B)),
          d = D (subgame f RC'.1 RC'.2) }
        = {D (subgame f RC.1 RC.2)} := by
    ext d
    constructor
    · rintro ⟨RC', hRC', rfl⟩
      rw [Set.mem_singleton_iff] at hRC'
      subst hRC'
      rfl
    · intro hd
      rw [Set.mem_singleton_iff] at hd
      exact ⟨RC, Set.mem_singleton RC, hd⟩
  rw [hset, csInf_singleton]

private lemma seedGame_eq_M0 : seedGame = M0 := by
  funext x y
  fin_cases y <;> simp [seedGame, M0]

private lemma equipartition_image_inj {I K X : Type*} [DecidableEq I] [DecidableEq K]
    [DecidableEq X] (f : I → K) (hf : Function.Injective f)
    (R : Finset (I × X)) (Q : Finset I) {T : ℕ}
    (h : IsEquipartitionedGE R Q T) :
    IsEquipartitionedGE (R.image (fun p : I × X => (f p.1, p.2))) (Q.image f) T := by
  classical
  intro k hk
  rcases Finset.mem_image.mp hk with ⟨q, hq, rfl⟩
  let F : I × X → K × X := fun p => (f p.1, p.2)
  have hFinj : Function.Injective F := by
    intro a b hab
    apply Prod.ext
    · apply hf
      exact congrArg (fun z : K × X => z.1) hab
    · exact congrArg (fun z : K × X => z.2) hab
  have hfilter :
      ((R.image F).filter (fun p : K × X => p.1 = f q)) =
        (R.filter (fun p : I × X => p.1 = q)).image F := by
    rw [Finset.filter_image]
    congr 1
    ext p
    simp [F, hf.eq_iff]
  rw [hfilter]
  rw [Finset.card_image_of_injective]
  · exact h q hq
  · intro a b hab
    exact hFinj hab

private lemma eight_mul_le_two_pow {n : ℕ} (hn : 6 ≤ n) : 8 * n ≤ 2 ^ n := by
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

private lemma log_le_div_eight {k : ℕ} (hk : 64 ≤ k) :
    Nat.log 2 k ≤ k / 8 := by
  have hlog6 : 6 ≤ Nat.log 2 k := by
    calc 6 = Nat.log 2 64 := by norm_num [Nat.log]
      _ ≤ Nat.log 2 k := Nat.log_mono_right hk
  have h8 : 8 * Nat.log 2 k ≤ 2 ^ Nat.log 2 k := eight_mul_le_two_pow hlog6
  have hpow : 2 ^ Nat.log 2 k ≤ k := Nat.pow_log_le_self 2 (by omega)
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 8)]
  nlinarith

/-- Companion: the use-site numeric gates for `M1_low_column_stage2` follow from
the power-of-two large-`d` lane once `64 ≤ log₂ d`. -/
theorem M1_low_column_stage2_gates {d : ℕ} (hpow : IsPow2 d)
    (hlog : 64 ≤ Nat.log 2 d) :
    Params.q1 d + 2 = Params.r1 d * Params.t1 d ∧
    Nat.log 2 (Params.t1 d) ≤ Params.b1 d ∧
    Nat.log 2 (Params.r1 d) ≤ Params.b1 d ∧
    Params.b1 d + Nat.log 2 (Params.r2 d) + Nat.log 2 (Params.r1 d)
        + Nat.log 2 (Params.t1 d) + 8 ≤ Params.t1 d / 16 := by
  classical
  let k := Nat.log 2 d
  have hk64 : 64 ≤ k := by simpa [k] using hlog
  have hk1 : 1 ≤ k := by omega
  have htlo : 64 * k ≤ Params.t1 d := by
    simpa [k] using (Params.t1_bracket (d := d) (by simpa [k] using hk1)).1
  have hthi : Params.t1 d ≤ 128 * k := by
    simpa [k] using (Params.t1_bracket (d := d) (by simpa [k] using hk1)).2
  have hqhi : Params.q1 d + 2 ≤ 4 * k ^ 2 := by
    simpa [k] using Params.q1_add_two_le (d := d) (by simpa [k] using hk1)
  have hlogk8 : Nat.log 2 k ≤ k / 8 := log_le_div_eight hk64
  have hT_le_logk_add7 : Nat.log 2 (Params.t1 d) ≤ Nat.log 2 k + 7 := by
    have hklt : k < 2 ^ (Nat.log 2 k + 1) :=
      Nat.lt_pow_succ_log_self (b := 2) (by norm_num) k
    have htlt : Params.t1 d < 2 ^ (Nat.log 2 k + 8) := by
      calc Params.t1 d ≤ 128 * k := hthi
        _ < 128 * 2 ^ (Nat.log 2 k + 1) := by
            exact (Nat.mul_lt_mul_left (by norm_num : 0 < 128)).mpr hklt
        _ = 2 ^ (Nat.log 2 k + 8) := by
            rw [show 128 = (2 : ℕ) ^ 7 by norm_num, ← pow_add]
            congr 1
            omega
    have hltlog := Nat.log_lt_of_lt_pow (b := 2)
      (x := Nat.log 2 k + 8) (y := Params.t1 d)
      (Params.t1_pos d).ne' htlt
    omega
  have hT_bound : Nat.log 2 (Params.t1 d) ≤ k / 8 + 7 := by
    omega
  have hqeq : Params.q1 d + 2 = Params.r1 d * Params.t1 d :=
    Params.q1_add_two_eq_r1_mul_t1 (d := d) (by simpa [k] using hk64)
  have hr1_mul_bound : Params.r1 d * (64 * k) ≤ 4 * k ^ 2 := by
    calc Params.r1 d * (64 * k) ≤ Params.r1 d * Params.t1 d := by
          exact Nat.mul_le_mul_left _ htlo
      _ = Params.q1 d + 2 := hqeq.symm
      _ ≤ 4 * k ^ 2 := hqhi
  have h16r1 : 16 * Params.r1 d ≤ k := by
    nlinarith [hr1_mul_bound, hk1]
  have hr1_le_k16 : Params.r1 d ≤ k / 16 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 16)]
    simpa [mul_comm] using h16r1
  have hr1_le_k : Params.r1 d ≤ k := by
    have : k / 16 ≤ k := Nat.div_le_self _ _
    exact le_trans hr1_le_k16 this
  have hR_bound : Nat.log 2 (Params.r1 d) ≤ k / 8 := by
    exact le_trans (Nat.log_mono_right hr1_le_k) hlogk8
  have hlogr2 : Nat.log 2 (Params.r2 d) ≤ k := by
    have hr2le : Params.r2 d ≤ Params.q2 d := by
      unfold Params.r2
      exact Nat.div_le_self _ _
    have hle := Nat.log_mono_right (b := 2) hr2le
    simpa [k, Params.q2_eq_of_pow2 hpow] using hle
  have hb1eq : Params.b1 d = 2 * k := by
    unfold Params.b1
    rfl
  have hT_b1 : Nat.log 2 (Params.t1 d) ≤ Params.b1 d := by
    rw [hb1eq]
    omega
  have hR_b1 : Nat.log 2 (Params.r1 d) ≤ Params.b1 d := by
    rw [hb1eq]
    omega
  have ht_div : 4 * k ≤ Params.t1 d / 16 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 16)]
    nlinarith
  have hgap' : Params.b1 d + Nat.log 2 (Params.r2 d) + Nat.log 2 (Params.r1 d)
        + Nat.log 2 (Params.t1 d) + 8 ≤ Params.t1 d / 16 := by
    rw [hb1eq]
    omega
  exact ⟨hqeq, hT_b1, hR_b1, hgap'⟩

set_option maxHeartbeats 800000 in
-- The localized-extension instance leaves several arithmetic transports in one proof.

-- CLAIM-BEGIN lem:M1LowColumnStage2
/-- Paper `lem:M1LowColumnStage2`, residual Stage-1 hardness at Stage-2 densities:
with `h₂↓ := 2^{-(b₁ + log r₂)}`, for every power of two `1 ≤ r' ≤ r₁`,
any extraction `N = M₁[R'; C']` with `R'` a `(Q,1)`-equipartition,
`|Q| = (9/16) r' · t₁`, and `|C'| / |C₁| ≥ h₂↓` satisfies
`comp N ≥ comp M₀ + log t₁ + log r'`. The vehicle is `cor:localized-extension`
at `f = M₀`, `T = log t₁`, `R'ₑ = log r'`, `a = 0`,
`p_seed = (9/16)t₁`; the four numeric gates are checklist-deliverable
use-site hypotheses. -/
theorem M1_low_column_stage2 (d : ℕ) (hd : 2 ≤ d)
    (hchk : Params.t1 d ≤ Params.q1 d + 5)
    (hdiv : Params.q1 d + 2 = Params.r1 d * Params.t1 d)
    (hTb : Nat.log 2 (Params.t1 d) ≤ Params.b1 d)
    (hRb : Nat.log 2 (Params.r1 d) ≤ Params.b1 d)
    (hgap : Params.b1 d + Nat.log 2 (Params.r2 d) + Nat.log 2 (Params.r1 d)
        + Nat.log 2 (Params.t1 d) + 8 ≤ Params.t1 d / 16)
    {r' : ℕ} (hr'pow : ∃ k, r' = 2 ^ k) (_hr'1 : 1 ≤ r')
    (hr'r1 : r' ≤ Params.r1 d)
    (R' : Finset (R1 d)) (C' : Finset (C1 d))
    (Q : Finset (Fin (Params.q1 d)))
    (hQcard : 16 * Q.card = 9 * r' * Params.t1 d)
    (hrow : IsEquipartitionedGE
              (R'.image (fun a => ((a.1 : Fin (Params.q1 d)), a.2))) Q 1)
    (hcol : (2 : ℝ) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : ℤ))
              * (Fintype.card (C1 d) : ℝ) ≤ (C'.card : ℝ)) :
    (1 : ℤ) + (Nat.log 2 (Params.t1 d) : ℤ) + (Nat.log 2 r' : ℤ)
      ≤ (Dfamily (M1 d) {(R', C')} : ℤ) := by
-- CLAIM-END lem:M1LowColumnStage2
  classical
  let T := Nat.log 2 (Params.t1 d)
  let R := Nat.log 2 (Params.r1 d)
  let Re := Nat.log 2 r'
  let A := Params.b1 d + Nat.log 2 (Params.r2 d)
  let m := Params.t1 d / 16
  let pseed := 9 * m
  let ε := epsQT (Params.q1 d + 5) (Params.t1 d)
  let xseed : ℝ := (2 : ℝ) ^ (-(Params.b1 d : ℝ))
  let hden : ℝ := (2 : ℝ) ^ (-(A : ℤ))
  let hseed : ℝ := (2 : ℝ) ^ (-(((A + (T + 1) + 1 : ℕ) : ℝ)))

  have hk1 : 1 ≤ Nat.log 2 d := Nat.log_pos one_lt_two hd
  have hb1_ge1_nat : 1 ≤ Params.b1 d := by
    unfold Params.b1
    omega
  have hb : (1 : ℝ) ≤ (Params.b1 d : ℝ) := by exact_mod_cast hb1_ge1_nat
  have hb0 : (0 : ℝ) ≤ (Params.b1 d : ℝ) := by positivity
  have hTbR : (T : ℝ) ≤ (Params.b1 d : ℝ) := by
    exact_mod_cast (by simpa [T] using hTb)

  have ht1_clog : Params.t1 d = 2 ^ Nat.clog 2 (64 * Nat.log 2 d) := rfl
  have hT_eq : T = Nat.clog 2 (64 * Nat.log 2 d) := by
    unfold T
    rw [ht1_clog, log_two_pow]
  have ht1pow : Params.t1 d = 2 ^ T := by
    rw [hT_eq]
    rfl
  have ht1ge64 : 64 ≤ Params.t1 d := by
    have ht := (Params.t1_bracket (d := d) hk1).1
    have h64 : 64 ≤ 64 * Nat.log 2 d := by nlinarith
    exact le_trans h64 ht
  have hT6 : 6 ≤ T := by
    have hpow6 : 2 ^ 6 ≤ 2 ^ T := by
      rw [← ht1pow]
      norm_num
      exact ht1ge64
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow6
  have hdiv16 : 16 ∣ Params.t1 d := by
    refine ⟨2 ^ (T - 4), ?_⟩
    rw [ht1pow]
    have hTsplit : T = 4 + (T - 4) := by omega
    rw [hTsplit, pow_add]
    norm_num
  have h16 : Params.t1 d = 16 * m := by
    have hm := Nat.div_mul_cancel hdiv16
    unfold m
    omega
  have hmpos : 0 < m := by
    have htpos := Params.t1_pos d
    omega
  have hpseed_pos : 0 < pseed := by
    unfold pseed
    omega
  have hp1 : 2 ^ T ≤ 2 * pseed := by
    rw [← ht1pow, h16]
    unfold pseed
    omega
  have hp2 : pseed ≤ 2 ^ T := by
    rw [← ht1pow, h16]
    unfold pseed
    omega

  have hqpow : Params.q1 d + 2 = 2 ^ Params.a d := Params.q1_add_two_pow hk1
  have hr1dvd : Params.r1 d ∣ 2 ^ Params.a d := by
    rw [← hqpow]
    exact ⟨Params.t1 d, hdiv⟩
  obtain ⟨j, _hjle, hr1j⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hr1dvd
  have hr1pow : Params.r1 d = 2 ^ R := by
    unfold R
    rw [hr1j, log_two_pow]
  have hr'log : r' = 2 ^ Re := by
    unfold Re
    exact pow_two_log_eq_of_pow2 hr'pow
  have hcast : 2 ^ (R + T) = Params.q1 d + 2 := by
    calc 2 ^ (R + T) = 2 ^ R * 2 ^ T := by rw [pow_add]
      _ = Params.r1 d * Params.t1 d := by rw [← hr1pow, ← ht1pow]
      _ = Params.q1 d + 2 := hdiv.symm
  have hReR : Re ≤ R := by
    unfold Re R
    exact Nat.log_mono_right hr'r1

  have hgap' : A + R + T + 8 ≤ m := by
    unfold A R T m
    simpa using hgap
  have hqpos : 0 < Params.q1 d + 5 := by omega
  have hεpos : 0 < ε := by
    unfold ε
    exact epsQT_pos hqpos (Params.t1_pos d)
  have hεnonneg : 0 ≤ ε := le_of_lt hεpos
  have hεlt : ε < 1 := by
    unfold ε
    exact epsQT_lt_one hqpos (Params.t1_pos d)
  have hεden_pos : 0 < 1 + ε := by linarith

  have hx1 : (2 : ℝ) ^ (-(Params.b1 d : ℝ)) ≤ xseed := by rfl
  have hx2 : xseed ≤ 1 := by
    unfold xseed
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
    exact neg_nonpos.mpr (Nat.cast_nonneg _)
  have hx0 : 0 < xseed := by
    unfold xseed
    positivity
  have hh0 : 0 < hden := by
    unfold hden
    positivity
  have hh1 : hden ≤ 1 := by
    unfold hden
    rw [two_zpow_neg_nat_eq_rpow_neg_nat A]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
    exact neg_nonpos.mpr (Nat.cast_nonneg A)
  have hs0 : 0 < hseed := by
    unfold hseed
    positivity
  have hs1 : hseed ≤ 1 := by
    unfold hseed
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
    exact neg_nonpos.mpr (Nat.cast_nonneg _)

  let ι0 : Fin (2 ^ (R + T)) → Fin (Params.q1 d + 5) :=
    fun γ => Fin.castLE (by omega : Params.q1 d + 2 ≤ Params.q1 d + 5)
      (Fin.cast hcast γ)
  have hι0inj : Function.Injective ι0 := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg (fun x : Fin (Params.q1 d + 5) => x.val) hab
    simpa [ι0] using hv
  let S' : Fin (L1 d) → Fin (2 ^ (R + T)) → Fin 2 :=
    fun j γ => S1fam d j (ι0 γ)
  have hbal0 : IsBalancedFamily (Params.t1 d) (S1fam d) ε := by
    unfold ε
    exact S1fam_balanced d hchk
  have hproj := hbal0.projection ι0 hι0inj
  have hS : IsBalancedFamily (2 ^ T) S' ε := by
    simpa [S', ht1pow] using hproj

  have hbase_lower_of_le : ∀ c : ℕ, c ≤ R + T + 1 →
      (2 : ℝ) ^ (-(Params.t1 d : ℝ)) <
        hden * (2 : ℝ) ^ (-(c : ℝ)) / (1 + ε) := by
    intro c hc
    unfold hden
    apply stage2_base_lower (A := A) (c := c) (n := Params.t1 d) hεpos hεlt
    have hmt : m < Params.t1 d := by omega
    have hle : A + c + 1 ≤ A + R + T + 8 := by omega
    exact lt_of_le_of_lt (le_trans hle hgap') hmt
  have hbase_upper : ∀ c : ℕ,
      hden * (2 : ℝ) ^ (-(c : ℝ)) / (1 + ε) ≤ 1 := by
    intro c
    unfold hden
    exact stage2_base_le_one (A := A) (c := c) hεnonneg

  have hyi_lo : 1 / 2 < yLoss ε (2 ^ T) hden ((R + T) + D M0) := by
    apply half_lt_yLoss
    · positivity
    · rw [D_M0_eq_one]
      rw [← ht1pow]
      exact hbase_lower_of_le (R + T + 1) (by omega)
  have hyi_hi : yLoss ε (2 ^ T) hden ((R + T) + D M0) ≤ 1 := by
    apply yLoss_le_one
    · positivity
    · rw [D_M0_eq_one]
      exact hbase_upper (R + T + 1)
  have hyii_lo : ∀ c ≤ T, 1 / 2 < yLoss ε (2 ^ T) hden c := by
    intro c hc
    apply half_lt_yLoss
    · positivity
    · rw [← ht1pow]
      exact hbase_lower_of_le c (by omega)
  have hyii_hi : ∀ c ≤ T, yLoss ε (2 ^ T) hden c ≤ 1 := by
    intro c _hc
    apply yLoss_le_one
    · positivity
    · exact hbase_upper c
  have hres : IsColumnLossResilient M0 (Params.b1 d : ℝ) ε (R + T) T hden :=
    M0_column_loss_resilient (Params.b1 d : ℝ) ε (R + T) T hden
      hb0 hyi_lo hyi_hi hyii_lo hyii_hi

  have hlogb_hseed : Real.logb 2 hseed = -(((A + T + 2 : ℕ) : ℝ)) := by
    unfold hseed
    rw [Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]
    have hnat : A + (T + 1) + 1 = A + T + 2 := by omega
    rw [hnat]
  let z : ℝ := (pseed : ℝ) + Real.logb 2 hseed
  have hz_eq : z = (pseed : ℝ) - (((A + T + 2 : ℕ) : ℝ)) := by
    unfold z
    rw [hlogb_hseed]
    ring
  have hz_gt_8m : (8 * m : ℝ) < z := by
    rw [hz_eq]
    have hAle : A + T + 2 + 6 ≤ m := by omega
    have hAleR : ((A + T + 2 + 6 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hAle
    have hAleR' : ((A + T + 2 : ℕ) : ℝ) + 6 ≤ (m : ℝ) := by
      norm_num at hAleR ⊢
      exact hAleR
    have hAlt : ((A + T + 2 : ℕ) : ℝ) < (m : ℝ) := by linarith
    unfold pseed
    calc (8 * m : ℝ) = 9 * (m : ℝ) - (m : ℝ) := by ring
      _ < 9 * (m : ℝ) - ((A + T + 2 : ℕ) : ℝ) := by linarith
      _ = ((9 * m : ℕ) : ℝ) - ((A + T + 2 : ℕ) : ℝ) := by norm_num
  have h8m_eq : (8 * m : ℝ) = (2 : ℝ) ^ ((T : ℝ) - 1) := by
    have h16R : (Params.t1 d : ℝ) = 16 * (m : ℝ) := by exact_mod_cast h16
    calc (8 * m : ℝ) = (16 * (m : ℝ)) / 2 := by ring
      _ = (Params.t1 d : ℝ) / 2 := by rw [h16R]
      _ = ((2 ^ T : ℕ) : ℝ) / 2 := by rw [ht1pow]
      _ = (2 : ℝ) ^ (T : ℝ) / 2 := by
          rw [Real.rpow_natCast]
          norm_num
      _ = (2 : ℝ) ^ ((T : ℝ) - 1) := by
          rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  have hz_gt_pow : (2 : ℝ) ^ ((T : ℝ) - 1) < z := by
    rwa [← h8m_eq]
  have hzpos : 0 < z := lt_trans (by positivity) hz_gt_pow
  have hlog_gt : (T : ℝ) - 1 < Real.logb 2 z := by
    have htmp := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
      (by positivity : 0 < (2 : ℝ) ^ ((T : ℝ) - 1)) hz_gt_pow
    rwa [Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] at htmp
  have hceilT : (T : ℤ) ≤ ⌈Real.logb 2 z⌉ := by
    have hceil_gt : ((T : ℤ) - 1) < ⌈Real.logb 2 z⌉ := by
      rw [Int.lt_ceil]
      norm_num
      exact hlog_gt
    omega
  have hrank := rankclaim (p := pseed) hpseed_pos (x := xseed) (y := hseed)
    hx0 hx2 hs0 hs1 (by simpa [z] using hzpos)
  rw [seedGame_eq_M0] at hrank
  have hseedbd : D M0 + T ≤
      Dfamily (interlaceFun M0 pseed) (bracketGE (Fin 1) (Fin 2) pseed xseed hseed) := by
    have hZ : ((D M0 + T : ℕ) : ℤ) ≤
        (Dfamily (interlaceFun M0 pseed)
          (bracketGE (Fin 1) (Fin 2) pseed xseed hseed) : ℤ) := by
      rw [D_M0_eq_one]
      have hZ' : (1 : ℤ) + (T : ℤ) ≤
          (Dfamily (interlaceFun M0 pseed)
            (bracketGE (Fin 1) (Fin 2) pseed xseed hseed) : ℤ) := by
        linarith
      simpa using hZ'
    exact_mod_cast hZ
  have hbridge : hseed ≤
      hden * (2 : ℝ) ^ (-((T + D M0 : ℕ) : ℝ)) / (1 + ε) := by
    rw [D_M0_eq_one]
    unfold hseed hden
    have hb := stage2_bridge_base (A := A) (c := T + 1) hεpos hεlt
    exact hb

  let ι : Fin (Params.q1 d) → Fin (2 ^ (R + T)) :=
    fun i => Fin.cast hcast.symm
      (Fin.castLE (by omega : Params.q1 d ≤ Params.q1 d + 2) i)
  have hιinj : Function.Injective ι := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg (fun x : Fin (2 ^ (R + T)) => x.val) hab
    simpa [ι] using hv
  have hι0ι : ∀ i : Fin (Params.q1 d), ι0 (ι i) = baseIdx d i := by
    intro i
    apply Fin.ext
    simp [ι0, ι, baseIdx]
  let Rs : Finset (Fin (2 ^ (R + T)) × Fin 1) :=
    R'.image (fun a : R1 d => (ι a.1, a.2))
  have hrowR : IsEquipartitionedGE R' Q 1 := by
    simpa using hrow
  have hQcard' : Q.card = 2 ^ Re * pseed := by
    have hright : 9 * r' * Params.t1 d = 16 * (2 ^ Re * pseed) := by
      rw [hr'log, h16]
      unfold pseed
      ring
    have h16Q : 16 * Q.card = 16 * (2 ^ Re * pseed) := hQcard.trans hright
    exact Nat.mul_left_cancel (by norm_num : 0 < 16) h16Q
  have hRe_b : Re ≤ Params.b1 d := le_trans hReR (by simpa [R] using hRb)
  have hceil_one :
      ⌈(2 : ℝ) ^ (Re : ℕ) * xseed * (Fintype.card (Fin 1) : ℝ)⌉₊ = 1 := by
    have xpos : 0 < (2 : ℝ) ^ (Re : ℕ) * xseed * (Fintype.card (Fin 1) : ℝ) := by
      unfold xseed
      positivity
    have xle : (2 : ℝ) ^ (Re : ℕ) * xseed * (Fintype.card (Fin 1) : ℝ) ≤ 1 := by
      simp only [Fintype.card_fin, Nat.cast_one, mul_one]
      unfold xseed
      have heq : (2 : ℝ) ^ (Re : ℕ) * (2 : ℝ) ^ (-(Params.b1 d : ℝ)) =
          (2 : ℝ) ^ ((Re : ℝ) - (Params.b1 d : ℝ)) := by
        rw [← Real.rpow_natCast]
        rw [(Real.rpow_add (by norm_num : (0 : ℝ) < 2) (Re : ℝ)
          (-(Params.b1 d : ℝ))).symm]
        congr 1
      rw [heq, show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) by rw [Real.rpow_zero]]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      exact sub_nonpos.mpr (by exact_mod_cast hRe_b)
    exact le_antisymm (by rw [Nat.ceil_le]; simpa using xle) (Nat.one_le_ceil_iff.mpr xpos)
  have hceil_one' : ⌈(2 : ℝ) ^ (Re : ℕ) * xseed⌉₊ = 1 := by
    simpa using hceil_one
  have hRs : ∃ Qs : Finset (Fin (2 ^ (R + T))), Qs.card = 2 ^ Re * pseed ∧
      IsEquipartitionedGE Rs Qs
        ⌈(2 : ℝ) ^ (Re : ℕ) * xseed * (Fintype.card (Fin 1) : ℝ)⌉₊ := by
    refine ⟨Q.image ι, ?_, ?_⟩
    · rw [Finset.card_image_of_injective Q hιinj, hQcard']
    · simpa [Rs, hceil_one'] using equipartition_image_inj ι hιinj R' Q hrowR
  have hCs : hden * (2 : ℝ) ^ (-((0 : ℕ) : ℝ)) * (L1 d : ℝ) ≤ (C'.card : ℝ) := by
    unfold hden A
    simpa [C1] using hcol

  have hmain : D M0 + (Re + T) ≤
      D (subgame (relaxedInterlace M0 S') Rs C') :=
    localized_extension (X := Fin 1) (Y := Fin 2) (f := M0)
      (b := (Params.b1 d : ℝ)) (ε := ε) hb hεnonneg T R hTbR
      (S := S') hS pseed (xseed := xseed) (h := hden) (hseed := hseed)
      hx1 hx2 hh0 hh1 hs0 hs1 hp1 hp2 hres hseedbd hbridge
      0 Re (by omega) hReR Rs C' hRs hCs

  let rowMap : R1 d → Fin (2 ^ (R + T)) × Fin 1 := fun a => (ι a.1, a.2)
  have hrowMap_inj : Function.Injective rowMap := by
    intro a b hab
    apply Prod.ext
    · apply hιinj
      exact congrArg (fun z : Fin (2 ^ (R + T)) × Fin 1 => z.1) hab
    · exact Subsingleton.elim _ _
  let eRows : {a // a ∈ R'} ≃ {a // a ∈ Rs} :=
    Equiv.ofBijective
      (fun a : {a // a ∈ R'} => ⟨rowMap a.1, by
        exact Finset.mem_image_of_mem (fun a : R1 d => (ι a.1, a.2)) a.2⟩)
      (by
        constructor
        · intro a b hab
          apply Subtype.ext
          apply hrowMap_inj
          exact congrArg (fun z : {a // a ∈ Rs} => z.1) hab
        · intro y
          rcases y with ⟨y, hy⟩
          change y ∈ R'.image (fun a : R1 d => (ι a.1, a.2)) at hy
          rcases Finset.mem_image.mp hy with ⟨x, hx, hxy⟩
          refine ⟨⟨x, hx⟩, ?_⟩
          apply Subtype.ext
          exact hxy)
  have hgame :
      (fun a b => subgame (relaxedInterlace M0 S') Rs C' (eRows a) b)
        = subgame (M1 d) R' C' := by
    funext a b
    simp [subgame, relaxedInterlace, S', M1, M1hat, rowMap, eRows, hι0ι]
  have hDinv := D_equiv_invariance (subgame (relaxedInterlace M0 S') Rs C')
    eRows (Equiv.refl {c // c ∈ C'})
  have hDrel : D (subgame (M1 d) R' C') =
      D (subgame (relaxedInterlace M0 S') Rs C') := by
    rw [← hgame]
    exact hDinv
  have hfam : Dfamily (M1 d) {(R', C')} = D (subgame (M1 d) R' C') :=
    dfamily_singleton_local (M1 d) (R', C')
  have hNat : 1 + T + Re ≤ Dfamily (M1 d) {(R', C')} := by
    rw [D_M0_eq_one] at hmain
    rw [← hDrel, ← hfam] at hmain
    omega
  have hInt : (1 : ℤ) + (T : ℤ) + (Re : ℤ) ≤
      (Dfamily (M1 d) {(R', C')} : ℤ) := by
    exact_mod_cast hNat
  simpa [T, Re, add_assoc] using hInt

/-- Companion for `cor:M1-complexity`: any residual Stage-1 slice certified by
`M1_low_column_stage2` lower-bounds the ambient matrix `M1`, since subgames
cannot be harder than the full game. The remaining `cor:M1-complexity` work is
to supply the canonical dense slice at `r' = r1`. -/
theorem M1_ambient_lower_of_stage2_slice (d : ℕ) (hd : 2 ≤ d)
    (hchk : Params.t1 d ≤ Params.q1 d + 5)
    (hdiv : Params.q1 d + 2 = Params.r1 d * Params.t1 d)
    (hTb : Nat.log 2 (Params.t1 d) ≤ Params.b1 d)
    (hRb : Nat.log 2 (Params.r1 d) ≤ Params.b1 d)
    (hgap : Params.b1 d + Nat.log 2 (Params.r2 d) + Nat.log 2 (Params.r1 d)
        + Nat.log 2 (Params.t1 d) + 8 ≤ Params.t1 d / 16)
    {r' : ℕ} (hr'pow : ∃ k, r' = 2 ^ k) (hr'1 : 1 ≤ r')
    (hr'r1 : r' ≤ Params.r1 d)
    (R' : Finset (R1 d)) (C' : Finset (C1 d))
    (Q : Finset (Fin (Params.q1 d)))
    (hQcard : 16 * Q.card = 9 * r' * Params.t1 d)
    (hrow : IsEquipartitionedGE
              (R'.image (fun a => ((a.1 : Fin (Params.q1 d)), a.2))) Q 1)
    (hcol : (2 : ℝ) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : ℤ))
              * (Fintype.card (C1 d) : ℝ) ≤ (C'.card : ℝ)) :
    (1 : ℤ) + (Nat.log 2 (Params.t1 d) : ℤ) + (Nat.log 2 r' : ℤ)
      ≤ (D (M1 d) : ℤ) := by
  have hslice := M1_low_column_stage2 d hd hchk hdiv hTb hRb hgap
    hr'pow hr'1 hr'r1 R' C' Q hQcard hrow hcol
  rw [dfamily_singleton_local] at hslice
  have hsub : D (subgame (M1 d) R' C') ≤ D (M1 d) := D_subgame_le (M1 d) R' C'
  exact le_trans hslice (by exact_mod_cast hsub)

/-- Companion for `cor:M1-complexity`: once the canonical full-density
`r' = r₁` slice data is supplied, `M1_low_column_stage2` gives the lower half
of `comp M₁ = a+1`. -/
theorem M1_capacity_lower_of_stage2_r1_slice (d : ℕ) (hd : 2 ≤ d)
    (hchk : Params.t1 d ≤ Params.q1 d + 5)
    (hdiv : Params.q1 d + 2 = Params.r1 d * Params.t1 d)
    (hTb : Nat.log 2 (Params.t1 d) ≤ Params.b1 d)
    (hRb : Nat.log 2 (Params.r1 d) ≤ Params.b1 d)
    (hgap : Params.b1 d + Nat.log 2 (Params.r2 d) + Nat.log 2 (Params.r1 d)
        + Nat.log 2 (Params.t1 d) + 8 ≤ Params.t1 d / 16)
    (hr1pow : ∃ k, Params.r1 d = 2 ^ k) (hr1pos : 1 ≤ Params.r1 d)
    (R' : Finset (R1 d)) (C' : Finset (C1 d))
    (Q : Finset (Fin (Params.q1 d)))
    (hQcard : 16 * Q.card = 9 * Params.r1 d * Params.t1 d)
    (hrow : IsEquipartitionedGE
              (R'.image (fun a => ((a.1 : Fin (Params.q1 d)), a.2))) Q 1)
    (hcol : (2 : ℝ) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : ℤ))
              * (Fintype.card (C1 d) : ℝ) ≤ (C'.card : ℝ)) :
    Params.a d + 1 ≤ D (M1 d) := by
  have hamb := M1_ambient_lower_of_stage2_slice d hd hchk hdiv hTb hRb hgap
    hr1pow hr1pos (le_refl (Params.r1 d)) R' C' Q hQcard hrow hcol
  have hcap := M1_capacity_log_identity d hd hdiv
  have hInt : ((Params.a d + 1 : ℕ) : ℤ) ≤ (D (M1 d) : ℤ) := by
    calc ((Params.a d + 1 : ℕ) : ℤ)
        = (1 : ℤ) + (Nat.log 2 (Params.t1 d) : ℤ)
            + (Nat.log 2 (Params.r1 d) : ℤ) := by
            rw [hcap]
            omega
      _ ≤ (D (M1 d) : ℤ) := hamb
  exact_mod_cast hInt

/-- Companion for the terminal one-copy lemma: a `p = 1` interlace subgame
projects to the base game without increasing deterministic complexity. -/
theorem M1_interlace_one_project_le {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (f : X → Y → Bool)
    (R0 : Finset (Fin 1 × X)) (C0 : Finset (Fin 1 → Y)) :
    D (subgame f (R0.image (fun a => a.2)) (C0.image (fun c => c 0))) ≤
      D (subgame (interlaceFun f 1) R0 C0) := by
  classical
  let preR : {x // x ∈ R0.image (fun a : Fin 1 × X => a.2)} → {a // a ∈ R0} :=
    fun x =>
      let w := Classical.choose (Finset.mem_image.mp x.2)
      ⟨w, (Classical.choose_spec (Finset.mem_image.mp x.2)).1⟩
  let preC : {y // y ∈ C0.image (fun c : Fin 1 → Y => c 0)} → {c // c ∈ C0} :=
    fun y =>
      let w := Classical.choose (Finset.mem_image.mp y.2)
      ⟨w, (Classical.choose_spec (Finset.mem_image.mp y.2)).1⟩
  have heq :
      subgame f (R0.image (fun a : Fin 1 × X => a.2))
          (C0.image (fun c : Fin 1 → Y => c 0)) =
        (fun x y => subgame (interlaceFun f 1) R0 C0 (preR x) (preC y)) := by
    funext x y
    have hx : (preR x).1.2 = x.1 := by
      dsimp [preR]
      exact (Classical.choose_spec (Finset.mem_image.mp x.2)).2
    have hy : (preC y).1 0 = y.1 := by
      dsimp [preC]
      exact (Classical.choose_spec (Finset.mem_image.mp y.2)).2
    have hfin : (preR x).1.1 = 0 := Subsingleton.elim _ _
    change f x.1 y.1 = f (preR x).1.2 ((preC y).1 (preR x).1.1)
    rw [hfin, hx, hy]
  rw [heq]
  exact D_mapNodes_le (subgame (interlaceFun f 1) R0 C0) preR preC

/-- Companion for `cor:M1-complexity`: the canonical full-density
`r' = r1` slice exists in `M1`, so the Stage-2 residual lower bound supplies
the lower half of the exact complexity of `M1`. -/
theorem M1_capacity_lower_canonical (d : ℕ) (hpow : IsPow2 d)
    (hlog : 64 ≤ Nat.log 2 d) :
    Params.a d + 1 ≤ D (M1 d) := by
  classical
  have hd : 2 ≤ d := by
    obtain ⟨k, rfl⟩ := hpow
    have hk : 64 ≤ k := by simpa [log_two_pow] using hlog
    exact Nat.succ_le_of_lt (Nat.one_lt_two_pow (by omega : k ≠ 0))
  have hchk : Params.t1 d ≤ Params.q1 d + 5 :=
    Params.t1_le_q1_add_five hlog
  obtain ⟨hdiv, hTb, hRb, hgap⟩ := M1_low_column_stage2_gates hpow hlog
  have hr1pow : ∃ k, Params.r1 d = 2 ^ k := by
    have hqpow : Params.q1 d + 2 = 2 ^ Params.a d := (Params.two_pow_a hd).symm
    have hr1dvd : Params.r1 d ∣ 2 ^ Params.a d := by
      rw [hqpow.symm]
      exact ⟨Params.t1 d, hdiv⟩
    obtain ⟨j, _hjle, hr1j⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hr1dvd
    exact ⟨j, hr1j⟩
  have hr1pos : 1 ≤ Params.r1 d := by
    obtain ⟨k, hk⟩ := hr1pow
    rw [hk]
    exact Nat.one_le_two_pow
  obtain ⟨n, hn_eq⟩ : ∃ n : ℕ, 16 * n = 9 * Params.r1 d * Params.t1 d := by
    refine ⟨9 * Params.r1 d * Params.t1 d / 16, ?_⟩
    have ht1_clog : Params.t1 d = 2 ^ Nat.clog 2 (64 * Nat.log 2 d) := rfl
    have ht1pow : Params.t1 d = 2 ^ Nat.log 2 (Params.t1 d) := by
      rw [ht1_clog, log_two_pow]
    have hlog1 : 1 ≤ Nat.log 2 d := by omega
    have ht1ge16 : 16 ≤ Params.t1 d := by
      have ht := (Params.t1_bracket (d := d) hlog1).1
      nlinarith
    have hlogt_ge4 : 4 ≤ Nat.log 2 (Params.t1 d) := by
      calc 4 = Nat.log 2 16 := by norm_num [Nat.log]
        _ ≤ Nat.log 2 (Params.t1 d) := Nat.log_mono_right ht1ge16
    have hdiv16 : 16 ∣ Params.t1 d := by
      rw [show 16 = (2 : ℕ) ^ 4 by norm_num, ht1pow]
      exact pow_dvd_pow 2 hlogt_ge4
    have hdiv16prod : 16 ∣ 9 * Params.r1 d * Params.t1 d := by
      exact dvd_mul_of_dvd_right hdiv16 (9 * Params.r1 d)
    rw [mul_comm, Nat.div_mul_cancel hdiv16prod]
  have hn_le : n ≤ (Finset.univ : Finset (Fin (Params.q1 d))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    have hqt : Params.q1 d + 2 = Params.r1 d * Params.t1 d := hdiv
    have hprod_ge5 : 5 ≤ Params.r1 d * Params.t1 d := by
      rw [← hqt]
      have hqlo := Params.le_q1_add_two (d := d) (by omega : 1 ≤ Nat.log 2 d)
      have hsmall : 5 ≤ 2 * Nat.log 2 d ^ 2 := by nlinarith
      omega
    have hmain_plus : n + 2 ≤ Params.r1 d * Params.t1 d := by
      have hn16 : 16 * n = 9 * Params.r1 d * Params.t1 d := hn_eq
      have hn16lin : 16 * n = 9 * (Params.r1 d * Params.t1 d) := by
        simpa [Nat.mul_assoc] using hn16
      omega
    have hmain : n ≤ Params.r1 d * Params.t1 d - 2 := by
      omega
    omega
  obtain ⟨Q, _hQsub, hQcard'⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin (Params.q1 d)))) hn_le
  let R' : Finset (R1 d) := Q.product (Finset.univ : Finset (Fin 1))
  let C' : Finset (C1 d) := Finset.univ
  have hQcard : 16 * Q.card = 9 * Params.r1 d * Params.t1 d := by
    rw [hQcard', hn_eq]
  have hrow : IsEquipartitionedGE
              (R'.image (fun a => ((a.1 : Fin (Params.q1 d)), a.2))) Q 1 := by
    intro q hq
    apply Nat.succ_le_of_lt
    exact Finset.card_pos.mpr ⟨(q, 0), by simp [R', hq]⟩
  have hcol : (2 : ℝ) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : ℤ))
              * (Fintype.card (C1 d) : ℝ) ≤ (C'.card : ℝ) := by
    dsimp [C']
    have hcoeff : (2 : ℝ) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : ℤ)) ≤ 1 := by
      let A : ℤ := (Params.b1 d + Nat.log 2 (Params.r2 d) : ℕ)
      change (2 : ℝ) ^ (-A) ≤ 1
      rw [zpow_neg]
      apply inv_le_one_of_one_le₀
      apply one_le_zpow₀
      · norm_num
      · dsimp [A]
        exact_mod_cast Nat.zero_le (Params.b1 d + Nat.log 2 (Params.r2 d))
    exact mul_le_of_le_one_left (by positivity) hcoeff
  exact M1_capacity_lower_of_stage2_r1_slice d hd hchk hdiv hTb hRb hgap
    hr1pow hr1pos R' C' Q hQcard hrow hcol

-- CLAIM-BEGIN cor:M1-complexity
/-- Paper `cor:M1-complexity`: at the Stage-1 large-`d` gate,
`comp M1 = comp M0 + log t1 + log r1 = a + 1 = B_cap`. The lower bound is
`M1_low_column_stage2` on the canonical full-density `r' = r1` slice; the
upper bound is the row-identification protocol. -/
theorem M1_complexity (d : ℕ) (hpow : IsPow2 d)
    (hlog : 64 ≤ Nat.log 2 d) :
    D (M1 d) = Params.a d + 1 := by
-- CLAIM-END cor:M1-complexity
  have hd : 2 ≤ d := by
    obtain ⟨k, rfl⟩ := hpow
    have hk : 64 ≤ k := by simpa [log_two_pow] using hlog
    exact Nat.succ_le_of_lt (Nat.one_lt_two_pow (by omega : k ≠ 0))
  exact le_antisymm (M1_upper_bound d hd) (M1_capacity_lower_canonical d hpow hlog)

/-- The Stage-2 terminal one-copy density used for `M1`. -/
noncomputable def M1_stage2_terminal_density (d : ℕ) : ℝ :=
  yLoss (epsQT (Params.q2 d) (Params.t2 d)) (Params.t2 d) (Params.h2 d)
    (Nat.log 2 (Params.q2 d) + D (M1 d))

set_option maxHeartbeats 800000 in
-- CLAIM-BEGIN lem:M1TerminalStage2
/-- Paper `lem:M1TerminalStage2`, with the App-C terminal-density estimates
left as explicit numeric gates: if the terminal row density supplies the
`(9/16)t1` rows required by `M1_low_column_stage2`, and the one-copy column
threshold dominates the Stage-2 residual density, then the terminal one-copy
family has complexity at least `comp M1 - log r1`. -/
theorem M1_terminal_stage2 (d : ℕ) (hpow : IsPow2 d)
    (hlog : 64 ≤ Nat.log 2 d)
    (hy_le_one : M1_stage2_terminal_density d ≤ 1)
    (hrowTerm : 9 * Params.t1 d ≤
      16 * ⌈(Fintype.card (R1 d) : ℝ) * M1_stage2_terminal_density d⌉₊)
    (hcolTerm : (2 : ℝ) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : ℤ))
        * (Fintype.card (C1 d) : ℝ) ≤
      (⌈(Fintype.card (C1 d) : ℝ) *
        ((2 : ℝ) ^ (-(Params.b1 d : ℤ)))⌉₊ : ℝ)) :
    (D (M1 d) : ℤ) - (Nat.log 2 (Params.r1 d) : ℤ) ≤
      (Dfamily (interlaceFun (M1 d) 1)
        (bracketGE (R1 d) (C1 d) 1 (M1_stage2_terminal_density d)
          ((2 : ℝ) ^ (-(Params.b1 d : ℤ)))) : ℤ) := by
-- CLAIM-END lem:M1TerminalStage2
  classical
  have hd : 2 ≤ d := by
    obtain ⟨k, rfl⟩ := hpow
    have hk : 64 ≤ k := by simpa [log_two_pow] using hlog
    exact Nat.succ_le_of_lt (Nat.one_lt_two_pow (by omega : k ≠ 0))
  have hchk : Params.t1 d ≤ Params.q1 d + 5 :=
    Params.t1_le_q1_add_five hlog
  obtain ⟨hdiv, hTb, hRb, hgap⟩ := M1_low_column_stage2_gates hpow hlog
  obtain ⟨n, hn_eq⟩ : ∃ n : ℕ, 16 * n = 9 * Params.t1 d := by
    refine ⟨9 * Params.t1 d / 16, ?_⟩
    have ht1_clog : Params.t1 d = 2 ^ Nat.clog 2 (64 * Nat.log 2 d) := rfl
    have ht1pow : Params.t1 d = 2 ^ Nat.log 2 (Params.t1 d) := by
      rw [ht1_clog, log_two_pow]
    have hlog1 : 1 ≤ Nat.log 2 d := by omega
    have ht1ge16 : 16 ≤ Params.t1 d := by
      have ht := (Params.t1_bracket (d := d) hlog1).1
      nlinarith
    have hlogt_ge4 : 4 ≤ Nat.log 2 (Params.t1 d) := by
      calc 4 = Nat.log 2 16 := by norm_num [Nat.log]
        _ ≤ Nat.log 2 (Params.t1 d) := Nat.log_mono_right ht1ge16
    have hdiv16 : 16 ∣ Params.t1 d := by
      rw [show 16 = (2 : ℕ) ^ 4 by norm_num, ht1pow]
      exact pow_dvd_pow 2 hlogt_ge4
    have hdiv16prod : 16 ∣ 9 * Params.t1 d := by
      exact dvd_mul_of_dvd_right hdiv16 9
    rw [mul_comm, Nat.div_mul_cancel hdiv16prod]
  have hn_row_threshold :
      n ≤ ⌈(Fintype.card (R1 d) : ℝ) * M1_stage2_terminal_density d⌉₊ := by
    omega
  have hcomplex := M1_complexity d hpow hlog
  have hcap := M1_capacity_log_identity d hd hdiv
  have htarget_nat :
      1 + Nat.log 2 (Params.t1 d) ≤
        Dfamily (interlaceFun (M1 d) 1)
          (bracketGE (R1 d) (C1 d) 1 (M1_stage2_terminal_density d)
            ((2 : ℝ) ^ (-(Params.b1 d : ℤ)))) := by
    unfold Dfamily
    apply le_csInf
    · have hycol_le_one :
          ((2 : ℝ) ^ (-(Params.b1 d : ℤ))) ≤ 1 := by
        let A : ℤ := (Params.b1 d : ℕ)
        change (2 : ℝ) ^ (-A) ≤ 1
        rw [zpow_neg]
        apply inv_le_one_of_one_le₀
        apply one_le_zpow₀
        · norm_num
        · dsimp [A]
          exact_mod_cast Nat.zero_le (Params.b1 d)
      have hXcard : 1 ≤ Fintype.card (R1 d) := by
        rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
        simpa using Params.one_le_q1 (by omega : 2 ≤ Nat.log 2 d)
      rcases bracketGE.nonempty (X := R1 d) (Y := C1 d)
          1 (M1_stage2_terminal_density d) ((2 : ℝ) ^ (-(Params.b1 d : ℤ)))
          hy_le_one hycol_le_one hXcard with ⟨RC, hRC⟩
      exact ⟨D (subgame (interlaceFun (M1 d) 1) RC.1 RC.2), ⟨RC, hRC, rfl⟩⟩
    · intro z hz
      rcases hz with ⟨RC, hRC, rfl⟩
      rcases hRC with ⟨hrows, hcols⟩
      have hrowcard : n ≤ RC.1.card := by
        have h := hrows 0 (Finset.mem_univ 0)
        have hfilter : RC.1.filter (fun p : Fin 1 × R1 d => p.1 = 0) = RC.1 := by
          apply Finset.filter_true_of_mem
          intro p _hp
          exact Subsingleton.elim _ _
        rw [hfilter] at h
        exact le_trans hn_row_threshold h
      obtain ⟨R0, hR0sub, hR0card⟩ := Finset.exists_subset_card_eq hrowcard
      let R' : Finset (R1 d) := R0.image (fun a : Fin 1 × R1 d => a.2)
      let C' : Finset (C1 d) := RC.2.image (fun c : Fin 1 → C1 d => c 0)
      let Q : Finset (Fin (Params.q1 d)) := R'.image (fun a : R1 d => a.1)
      have hRcard : R'.card = n := by
        dsimp [R']
        rw [Finset.card_image_of_injective]
        · exact hR0card
        · intro a b hab
          apply Prod.ext
          · exact Subsingleton.elim _ _
          · exact hab
      have hQcard' : Q.card = n := by
        dsimp [Q]
        rw [Finset.card_image_of_injective]
        · exact hRcard
        · intro a b hab
          apply Prod.ext
          · exact hab
          · exact Subsingleton.elim _ _
      have hQcard : 16 * Q.card = 9 * 1 * Params.t1 d := by
        rw [hQcard', hn_eq]
      have hrow : IsEquipartitionedGE
              (R'.image (fun a => ((a.1 : Fin (Params.q1 d)), a.2))) Q 1 := by
        intro q hq
        apply Nat.succ_le_of_lt
        rcases Finset.mem_image.mp hq with ⟨r, hr, rfl⟩
        exact Finset.card_pos.mpr ⟨r, by simp [R', hr]⟩
      have hCcard : C'.card = RC.2.card := by
        dsimp [C']
        rw [Finset.card_image_of_injective]
        intro a b hab
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        rw [hi]
        exact hab
      have hcol : (2 : ℝ) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : ℤ))
              * (Fintype.card (C1 d) : ℝ) ≤ (C'.card : ℝ) := by
        rw [hCcard]
        have hcols' :
            (⌈(Fintype.card (C1 d) : ℝ) *
              ((2 : ℝ) ^ (-(Params.b1 d : ℤ)))⌉₊ : ℝ) ≤
                (RC.2.card : ℝ) := by
          exact_mod_cast (by simpa [pow_one] using hcols)
        exact le_trans hcolTerm hcols'
      have hr1pos : 1 ≤ Params.r1 d := by
        by_contra h
        have hr0 : Params.r1 d = 0 := by omega
        have : Params.q1 d + 2 = 0 := by
          rw [hdiv, hr0, zero_mul]
        omega
      have hslice := M1_low_column_stage2 d hd hchk hdiv hTb hRb hgap
        (r' := 1) ⟨0, by norm_num⟩ (by omega) hr1pos
        R' C' Q hQcard hrow hcol
      rw [dfamily_singleton_local] at hslice
      have hsliceNat : 1 + Nat.log 2 (Params.t1 d) ≤ D (subgame (M1 d) R' C') := by
        have hInt : ((1 + Nat.log 2 (Params.t1 d) : ℕ) : ℤ) ≤
            (D (subgame (M1 d) R' C') : ℤ) := by
          simpa using hslice
        exact_mod_cast hInt
      have hproj : D (subgame (M1 d) R' C') ≤
          D (subgame (interlaceFun (M1 d) 1) R0 RC.2) := by
        simpa [R', C'] using M1_interlace_one_project_le (M1 d) R0 RC.2
      have hmono : D (subgame (interlaceFun (M1 d) 1) R0 RC.2) ≤
          D (subgame (interlaceFun (M1 d) 1) RC.1 RC.2) := by
        exact D_subgame_mono (interlaceFun (M1 d) 1) hR0sub (fun _ h => h)
      exact le_trans hsliceNat (le_trans hproj hmono)
  have hleft : (D (M1 d) : ℤ) - (Nat.log 2 (Params.r1 d) : ℤ) =
      (1 + Nat.log 2 (Params.t1 d) : ℕ) := by
    have hDnat : D (M1 d) = Params.a d + 1 := hcomplex
    have hA : Params.a d = Nat.log 2 (Params.r1 d) + Nat.log 2 (Params.t1 d) := hcap
    omega
  rw [hleft]
  exact_mod_cast htarget_nat

-- CLAIM-BEGIN aux:m1-terminal-discharge
private theorem m1_terminal_exponent_budget (d : ℕ) (hpow : IsPow2 d)
    (hlog : 2 ^ 18 ≤ Nat.log 2 d) :
    Params.b2 d + (Nat.log 2 (Params.q2 d) + D (M1 d)) + 1 ≤
      (Nat.log 2 (Nat.log 2 d) - 6) * Params.t2 d := by
  classical
  let k := Nat.log 2 d
  let ell := Nat.log 2 k
  have hlog64 : 64 ≤ Nat.log 2 d := by
    nlinarith
  have hlog1 : 1 ≤ Nat.log 2 d := by omega
  have hd : 2 ≤ d := by
    obtain ⟨j, rfl⟩ := hpow
    have hj : 2 ^ 18 ≤ j := by simpa [log_two_pow] using hlog
    exact Nat.succ_le_of_lt (Nat.one_lt_two_pow (by omega : j ≠ 0))
  have hD : D (M1 d) = Params.a d + 1 := M1_complexity d hpow hlog64
  have hq2log : Nat.log 2 (Params.q2 d) = k := by
    dsimp [k]
    rw [Params.q2_eq_of_pow2 hpow]
  have hell18 : 18 ≤ ell := by
    dsimp [ell, k]
    calc 18 = Nat.log 2 (2 ^ 18) := by rw [log_two_pow]
      _ ≤ Nat.log 2 (Nat.log 2 d) := Nat.log_mono_right hlog
  have hellpos : 0 < ell := by omega
  have hpow_ell_le_k : 2 ^ ell ≤ k := by
    dsimp [ell]
    exact Nat.pow_log_le_self 2 (by omega : k ≠ 0)
  have h6ell : 6 * ell ≤ 2 ^ ell := six_mul_le_two_pow (by omega)
  have h5ell6 : 5 * ell + 6 ≤ k := by
    calc 5 * ell + 6 ≤ 6 * ell := by omega
      _ ≤ 2 ^ ell := h6ell
      _ ≤ k := hpow_ell_le_k
  have hqpow : Params.q1 d + 2 = 2 ^ Params.a d := Params.q1_add_two_pow hlog1
  have hqle : Params.q1 d + 2 ≤ 4 * k ^ 2 := by
    dsimp [k]
    exact Params.q1_add_two_le (d := d) hlog1
  have hk_lt_pow : k < 2 ^ (ell + 1) := by
    dsimp [ell]
    exact Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) k
  have hk_le_pow : k ≤ 2 ^ (ell + 1) := le_of_lt hk_lt_pow
  have hk2_le : k ^ 2 ≤ (2 ^ (ell + 1)) ^ 2 :=
    Nat.pow_le_pow_left hk_le_pow 2
  have h4k2_le : 4 * k ^ 2 ≤ 2 ^ (2 * ell + 4) := by
    calc 4 * k ^ 2 ≤ 4 * (2 ^ (ell + 1)) ^ 2 := Nat.mul_le_mul_left 4 hk2_le
      _ = 2 ^ (2 * ell + 4) := by
        calc 4 * (2 ^ (ell + 1)) ^ 2
            = 2 ^ 2 * (2 ^ (ell + 1)) ^ 2 := by norm_num
          _ = 2 ^ 2 * 2 ^ ((ell + 1) * 2) := by rw [pow_mul]
          _ = 2 ^ (2 + ((ell + 1) * 2)) := by rw [← pow_add]
          _ = 2 ^ (2 * ell + 4) := by ring_nf
  have ha_le : Params.a d ≤ 2 * ell + 4 := by
    have hpowle : 2 ^ Params.a d ≤ 2 ^ (2 * ell + 4) := by
      rw [← hqpow]
      exact le_trans hqle h4k2_le
    exact (Nat.pow_le_pow_iff_right (by norm_num : 2 ≤ 2)).mp hpowle
  let inner : ℕ :=
    (3 * k + ell - 1) / ell
  have hinner_le_t2 : inner ≤ Params.t2 d := by
    dsimp [inner, k, ell]
    unfold Params.t2
    exact le_ceilPowTwo _
  have hceil_mul : 3 * k ≤ inner * ell := by
    dsimp [inner]
    have hdivmod := Nat.div_add_mod' (3 * k + ell - 1) ell
    have hmodlt : (3 * k + ell - 1) % ell < ell := Nat.mod_lt _ hellpos
    omega
  have hkey_mul : (k + 5 * ell + 6) * ell ≤ (3 * k * (ell - 6)) := by
    have h18k : 18 * k ≤ ell * k := Nat.mul_le_mul_right k hell18
    have h18k' : 18 * k ≤ k * ell := by simpa [Nat.mul_comm] using h18k
    have hpart : (5 * ell + 6) * ell ≤ k * ell :=
      Nat.mul_le_mul_right ell h5ell6
    have hsub_expand :
        ((3 * k * (ell - 6) : ℕ) : ℤ) =
          (3 : ℤ) * k * ell - 18 * k := by
      have hell6 : 6 ≤ ell := by omega
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hell6]
      ring
    have hkeyZ :
        (((k + 5 * ell + 6) * ell : ℕ) : ℤ) ≤
          ((3 * k * (ell - 6) : ℕ) : ℤ) := by
      rw [hsub_expand]
      push_cast at h18k' hpart
      push_cast
      nlinarith
    exact_mod_cast hkeyZ
  have hbudget_small : k + 5 * ell + 6 ≤ (ell - 6) * inner := by
    apply Nat.le_of_mul_le_mul_right
    · calc
        (k + 5 * ell + 6) * ell ≤ 3 * k * (ell - 6) := hkey_mul
        _ ≤ (inner * ell) * (ell - 6) := by
          exact Nat.mul_le_mul_right (ell - 6) hceil_mul
        _ = ((ell - 6) * inner) * ell := by ring
    · exact hellpos
  have hbudget : k + 5 * ell + 6 ≤ (ell - 6) * Params.t2 d := by
    exact le_trans hbudget_small (Nat.mul_le_mul_left (ell - 6) hinner_le_t2)
  have hA :
      Params.b2 d + (Nat.log 2 (Params.q2 d) + D (M1 d)) + 1 ≤
        k + 5 * ell + 6 := by
    unfold Params.b2
    rw [hD, hq2log]
    dsimp [ell, k]
    nlinarith [ha_le]
  exact le_trans hA hbudget

private theorem m1_terminal_density_lower (d : ℕ) (hpow : IsPow2 d)
    (hlog : 2 ^ 18 ≤ Nat.log 2 d) :
    (2 : ℝ) ^ (-(Nat.log 2 (Nat.log 2 d) - 6 : ℝ)) ≤
      M1_stage2_terminal_density d := by
  classical
  let c : ℕ := Nat.log 2 (Params.q2 d) + D (M1 d)
  let A : ℕ := Params.b2 d + c + 1
  let t : ℕ := Params.t2 d
  let ε : ℝ := epsQT (Params.q2 d) (Params.t2 d)
  let base : ℝ := (Params.h2 d * (2 : ℝ) ^ (-(c : ℝ))) / (1 + ε)
  have htpos_nat : 0 < t := by dsimp [t]; exact Params.t2_pos d
  have hεle : ε ≤ 1 / 2 := by
    dsimp [ε]
    exact epsQT_le_half (Params.q2_pos d) (Params.t2_pos d)
  have hloglog6 : 6 ≤ Nat.log 2 (Nat.log 2 d) := by
    have hloglog18 : 18 ≤ Nat.log 2 (Nat.log 2 d) := by
      calc 18 = Nat.log 2 (2 ^ 18) := by rw [log_two_pow]
        _ ≤ Nat.log 2 (Nat.log 2 d) := Nat.log_mono_right hlog
    omega
  have hdenpos : 0 < 1 + ε := by
    have hεpos : 0 < ε := by
      dsimp [ε]
      exact epsQT_pos (Params.q2_pos d) (Params.t2_pos d)
    linarith
  have hnum_nonneg : 0 ≤ Params.h2 d * (2 : ℝ) ^ (-(c : ℝ)) := by
    exact mul_nonneg (le_of_lt Params.h2_pos) (by positivity)
  have hbase_ge_half :
      Params.h2 d * (2 : ℝ) ^ (-(c : ℝ)) / 2 ≤ base := by
    dsimp [base]
    exact div_le_div_of_nonneg_left hnum_nonneg hdenpos (by linarith)
  have hhalf_eq :
      Params.h2 d * (2 : ℝ) ^ (-(c : ℝ)) / 2 =
        (2 : ℝ) ^ (-(A : ℝ)) := by
    have htwo_pos : (0 : ℝ) < 2 := by norm_num
    have hcast_sum :
        (((Params.b2 d + c + 1 : ℕ) : ℝ)) =
          (Params.b2 d : ℝ) + (c : ℝ) + 1 := by
      norm_num
    dsimp [A]
    unfold Params.h2
    rw [← Real.rpow_intCast (2 : ℝ) (-(Params.b2 d : ℤ))]
    calc
      (2 : ℝ) ^ (((-(Params.b2 d : ℤ) : ℤ) : ℝ)) * (2 : ℝ) ^ (-(c : ℝ)) / 2
          = (2 : ℝ) ^ (-(Params.b2 d : ℤ) : ℝ) *
              (2 : ℝ) ^ (-(c : ℝ)) * (2 : ℝ) ^ (-1 : ℝ) := by
                rw [Real.rpow_neg_one, Int.cast_neg, Int.cast_natCast]
                ring_nf
      _ = (2 : ℝ) ^
            ((-(Params.b2 d : ℤ) : ℝ) + (-(c : ℝ)) + (-1 : ℝ)) := by
              rw [← Real.rpow_add htwo_pos, ← Real.rpow_add htwo_pos]
      _ = (2 : ℝ) ^ (-(((Params.b2 d + c + 1 : ℕ) : ℝ))) := by
              rw [hcast_sum]
              congr 1
              rw [Int.cast_natCast]
              ring_nf
  have hpowA_le_base : (2 : ℝ) ^ (-(A : ℝ)) ≤ base := by
    rw [← hhalf_eq]
    exact hbase_ge_half
  have hbudget : A ≤ (Nat.log 2 (Nat.log 2 d) - 6) * t := by
    dsimp [A, c, t]
    exact m1_terminal_exponent_budget d hpow hlog
  have hpow_budget :
      (2 : ℝ) ^ (-(((Nat.log 2 (Nat.log 2 d) - 6) * t : ℕ) : ℝ)) ≤
        (2 : ℝ) ^ (-(A : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    exact neg_le_neg (by exact_mod_cast hbudget)
  have hbase0 :
      0 ≤ (2 : ℝ) ^
        (-(((Nat.log 2 (Nat.log 2 d) - 6) * t : ℕ) : ℝ)) := by positivity
  have hroot_le :
      ((2 : ℝ) ^
        (-(((Nat.log 2 (Nat.log 2 d) - 6) * t : ℕ) : ℝ))) ^ (1 / (t : ℝ)) ≤
        base ^ (1 / (t : ℝ)) := by
    exact Real.rpow_le_rpow hbase0 (le_trans hpow_budget hpowA_le_base) (by positivity)
  have hroot_eq :
      ((2 : ℝ) ^
        (-(((Nat.log 2 (Nat.log 2 d) - 6) * t : ℕ) : ℝ))) ^ (1 / (t : ℝ)) =
        (2 : ℝ) ^ (-(Nat.log 2 (Nat.log 2 d) - 6 : ℝ)) := by
    have hcastmul :
        (((Nat.log 2 (Nat.log 2 d) - 6) * t : ℕ) : ℝ) =
          (Nat.log 2 (Nat.log 2 d) - 6 : ℝ) * (t : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_sub hloglog6]
      norm_num
    rw [hcastmul]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have htne : (t : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt htpos_nat
    congr 1
    field_simp [htne]
  unfold M1_stage2_terminal_density yLoss
  dsimp [base, ε, c, t] at hroot_le hroot_eq
  rw [← hroot_eq]
  exact hroot_le

/-- The terminal one-copy row density is at most one. -/
theorem M1_terminal_density_le_one (d : ℕ) :
    M1_stage2_terminal_density d ≤ 1 := by
  unfold M1_stage2_terminal_density
  apply yLoss_le_one
  · have hεnonneg : 0 ≤ epsQT (Params.q2 d) (Params.t2 d) := by
      exact le_of_lt (epsQT_pos (Params.q2_pos d) (Params.t2_pos d))
    have hdenpos : 0 < 1 + epsQT (Params.q2 d) (Params.t2 d) := by
      linarith
    have hh2nonneg : 0 ≤ Params.h2 d := le_of_lt Params.h2_pos
    have hpow_nonneg :
        0 ≤ (2 : ℝ) ^
          (-((Nat.log 2 (Params.q2 d) + D (M1 d) : ℕ) : ℝ)) := by
      positivity
    exact div_nonneg (mul_nonneg hh2nonneg hpow_nonneg) (le_of_lt hdenpos)
  · have hh2le : Params.h2 d ≤ 1 := by
      unfold Params.h2
      let A : ℤ := (Params.b2 d : ℕ)
      change (2 : ℝ) ^ (-A) ≤ 1
      rw [zpow_neg]
      apply inv_le_one_of_one_le₀
      apply one_le_zpow₀
      · norm_num
      · dsimp [A]
        exact_mod_cast Nat.zero_le (Params.b2 d)
    have hpowle :
        (2 : ℝ) ^
          (-((Nat.log 2 (Params.q2 d) + D (M1 d) : ℕ) : ℝ)) ≤ 1 := by
      have hexp :
          -((Nat.log 2 (Params.q2 d) + D (M1 d) : ℕ) : ℝ) ≤ (0 : ℝ) := by
        exact neg_nonpos.mpr (by positivity)
      calc
        (2 : ℝ) ^
            (-((Nat.log 2 (Params.q2 d) + D (M1 d) : ℕ) : ℝ))
            ≤ (2 : ℝ) ^ (0 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
        _ = 1 := by norm_num
    have hnum :
        Params.h2 d *
          (2 : ℝ) ^
            (-((Nat.log 2 (Params.q2 d) + D (M1 d) : ℕ) : ℝ)) ≤ 1 := by
      calc
        Params.h2 d *
          (2 : ℝ) ^
            (-((Nat.log 2 (Params.q2 d) + D (M1 d) : ℕ) : ℝ))
            ≤ 1 * 1 := by
              exact mul_le_mul hh2le hpowle (by positivity) (by positivity)
        _ = 1 := by norm_num
    have hεnonneg : 0 ≤ epsQT (Params.q2 d) (Params.t2 d) := by
      exact le_of_lt (epsQT_pos (Params.q2_pos d) (Params.t2_pos d))
    have hdenpos : 0 < 1 + epsQT (Params.q2 d) (Params.t2 d) := by
      linarith
    have hdenge : 1 ≤ 1 + epsQT (Params.q2 d) (Params.t2 d) := by
      linarith
    rw [div_le_iff₀ hdenpos]
    calc
      Params.h2 d *
          (2 : ℝ) ^
            (-((Nat.log 2 (Params.q2 d) + D (M1 d) : ℕ) : ℝ))
          ≤ 1 := hnum
      _ ≤ 1 * (1 + epsQT (Params.q2 d) (Params.t2 d)) := by nlinarith

/-- The terminal one-copy row density leaves enough `M1` rows for the
`r' = 1` residual Stage-1 slice. -/
theorem M1_terminal_row_estimate (d : ℕ) (hpow : IsPow2 d)
    (hlog : 2 ^ 18 ≤ Nat.log 2 d) :
    9 * Params.t1 d ≤
      16 * ⌈(Fintype.card (R1 d) : ℝ) * M1_stage2_terminal_density d⌉₊ := by
  classical
  let k := Nat.log 2 d
  let ell := Nat.log 2 k
  have hlog1 : 1 ≤ Nat.log 2 d := by nlinarith
  have hkpos_nat : 0 < k := by dsimp [k]; omega
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos_nat
  have hell6 : 6 ≤ ell := by
    dsimp [ell, k]
    have h18 : 18 ≤ Nat.log 2 (Nat.log 2 d) := by
      calc 18 = Nat.log 2 (2 ^ 18) := by rw [log_two_pow]
        _ ≤ Nat.log 2 (Nat.log 2 d) := Nat.log_mono_right hlog
    omega
  have hpow_ell_le_k : (2 : ℝ) ^ ell ≤ (k : ℝ) := by
    have hnat : 2 ^ ell ≤ k := by
      dsimp [ell]
      exact Nat.pow_log_le_self 2 (by omega : k ≠ 0)
    exact_mod_cast hnat
  have hpow_eq :
      (64 : ℝ) / ((2 : ℝ) ^ ell) =
        (2 : ℝ) ^ (-(ell - 6 : ℝ)) := by
    have hsplit : ell = (ell - 6) + 6 := by omega
    calc
      (64 : ℝ) / ((2 : ℝ) ^ ell)
          = (2 : ℝ) ^ 6 / ((2 : ℝ) ^ ((ell - 6) + 6)) := by
              rw [hsplit]; norm_num
      _ = (2 : ℝ) ^ 6 / ((2 : ℝ) ^ (ell - 6) * (2 : ℝ) ^ 6) := by
              rw [pow_add]
      _ = ((2 : ℝ) ^ (ell - 6))⁻¹ := by
              field_simp [(pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))]
      _ = (2 : ℝ) ^ (-(ell - 6 : ℝ)) := by
              rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
              have hsubcast : ((ell - 6 : ℕ) : ℝ) = (ell : ℝ) - 6 := by
                rw [Nat.cast_sub hell6]
                norm_num
              rw [← hsubcast]
              rw [Real.rpow_natCast]
  have h64_over_k :
      (64 : ℝ) / (k : ℝ) ≤ (2 : ℝ) ^ (-(ell - 6 : ℝ)) := by
    calc
      (64 : ℝ) / (k : ℝ) ≤ (64 : ℝ) / ((2 : ℝ) ^ ell) := by
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow_ell_le_k
      _ = (2 : ℝ) ^ (-(ell - 6 : ℝ)) := hpow_eq
  have hydens :
      (64 : ℝ) / (k : ℝ) ≤ M1_stage2_terminal_density d := by
    exact le_trans h64_over_k (by
      dsimp [ell, k]
      exact m1_terminal_density_lower d hpow hlog)
  have hcardR : (Fintype.card (R1 d) : ℝ) = (Params.q1 d : ℝ) := by
    simp [R1, Fintype.card_prod, Fintype.card_fin]
  have hq_lowerR : (2 : ℝ) * (k : ℝ) ^ 2 - 2 ≤ (Params.q1 d : ℝ) := by
    have hq := Params.le_q1_add_two (d := d) hlog1
    dsimp [k]
    have hqR : ((2 * Nat.log 2 d ^ 2 : ℕ) : ℝ) ≤ (Params.q1 d : ℝ) + 2 := by
      exact_mod_cast hq
    push_cast at hqR
    nlinarith
  have ht_upperR : (Params.t1 d : ℝ) ≤ 128 * (k : ℝ) := by
    have ht := (Params.t1_bracket (d := d) hlog1).2
    dsimp [k]
    exact_mod_cast ht
  have hk_two : (2 : ℝ) ≤ (k : ℝ) := by
    dsimp [k]
    exact_mod_cast (by nlinarith : 2 ≤ Nat.log 2 d)
  have hmain : 9 * (Params.t1 d : ℝ) * (k : ℝ) ≤
      1024 * (Params.q1 d : ℝ) := by
    nlinarith
  have hreal_row :
      ((9 * Params.t1 d : ℕ) : ℝ) / 16 ≤
        (Params.q1 d : ℝ) * ((64 : ℝ) / (k : ℝ)) := by
    field_simp [hkpos.ne']
    push_cast
    ring_nf
    nlinarith [hmain]
  have hreal :
      ((9 * Params.t1 d : ℕ) : ℝ) / 16 ≤
        (Fintype.card (R1 d) : ℝ) * M1_stage2_terminal_density d := by
    calc
      ((9 * Params.t1 d : ℕ) : ℝ) / 16
          ≤ (Params.q1 d : ℝ) * ((64 : ℝ) / (k : ℝ)) := hreal_row
      _ ≤ (Params.q1 d : ℝ) * M1_stage2_terminal_density d := by
          exact mul_le_mul_of_nonneg_left hydens (by positivity)
      _ = (Fintype.card (R1 d) : ℝ) * M1_stage2_terminal_density d := by
          rw [hcardR]
  have hceil :
      ((9 * Params.t1 d : ℕ) : ℝ) / 16 ≤
        (⌈(Fintype.card (R1 d) : ℝ) * M1_stage2_terminal_density d⌉₊ : ℝ) :=
    le_trans hreal (Nat.le_ceil _)
  have htargetR :
      ((9 * Params.t1 d : ℕ) : ℝ) ≤
        ((16 * ⌈(Fintype.card (R1 d) : ℝ) *
          M1_stage2_terminal_density d⌉₊ : ℕ) : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hceil (by norm_num : (0 : ℝ) ≤ 16)
    norm_num at hmul ⊢
    linarith
  exact_mod_cast htargetR

/-- The terminal Stage-2 column threshold is below the rounded one-copy
threshold used by `M1_terminal_stage2`. -/
theorem M1_terminal_col_estimate (d : ℕ) :
    (2 : ℝ) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : ℤ))
        * (Fintype.card (C1 d) : ℝ) ≤
      (⌈(Fintype.card (C1 d) : ℝ) *
        ((2 : ℝ) ^ (-(Params.b1 d : ℤ)))⌉₊ : ℝ) := by
  have hdown_le :
      (2 : ℝ) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : ℤ)) ≤
        (2 : ℝ) ^ (-(Params.b1 d : ℤ)) := by
    apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    omega
  calc
    (2 : ℝ) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : ℤ))
        * (Fintype.card (C1 d) : ℝ)
        ≤ (2 : ℝ) ^ (-(Params.b1 d : ℤ)) * (Fintype.card (C1 d) : ℝ) := by
          exact mul_le_mul_of_nonneg_right hdown_le (by positivity)
    _ = (Fintype.card (C1 d) : ℝ) * ((2 : ℝ) ^ (-(Params.b1 d : ℤ))) := by ring
    _ ≤ (⌈(Fintype.card (C1 d) : ℝ) *
        ((2 : ℝ) ^ (-(Params.b1 d : ℤ)))⌉₊ : ℝ) := Nat.le_ceil _

/-- Composability wrapper for `M1_terminal_stage2` with the terminal numeric
gates discharged under the explicit large-`d` logarithmic gate above. -/
theorem M1_terminal_stage2' (d : ℕ) (hpow : IsPow2 d)
    (hlog : 2 ^ 18 ≤ Nat.log 2 d) :
    (D (M1 d) : ℤ) - (Nat.log 2 (Params.r1 d) : ℤ) ≤
      (Dfamily (interlaceFun (M1 d) 1)
        (bracketGE (R1 d) (C1 d) 1 (M1_stage2_terminal_density d)
          ((2 : ℝ) ^ (-(Params.b1 d : ℤ)))) : ℤ) := by
  exact M1_terminal_stage2 d hpow (by nlinarith : 64 ≤ Nat.log 2 d)
    (M1_terminal_density_le_one d)
    (M1_terminal_row_estimate d hpow hlog)
    (M1_terminal_col_estimate d)
-- CLAIM-END aux:m1-terminal-discharge

end M1LowColumnStage2
section M1Robust

private theorem M1T_family_lower_from_slice (d : ℕ) (hd : 2 ≤ d)
    (hchk : Params.t1 d ≤ Params.q1 d + 5)
    (hdiv : Params.q1 d + 2 = Params.r1 d * Params.t1 d)
    (hTb : Nat.log 2 (Params.t1 d) ≤ Params.b1 d)
    (hRb : Nat.log 2 (Params.r1 d) ≤ Params.b1 d)
    (hgap : Params.b1 d + Nat.log 2 (Params.r2 d) + Nat.log 2 (Params.r1 d)
        + Nat.log 2 (Params.t1 d) + 8 ≤ Params.t1 d / 16)
    (β : ℝ) (hβle : β ≤ 1) {r' n : ℕ}
    (hr'pow : ∃ k, r' = 2 ^ k) (hr'1 : 1 ≤ r') (hr'r1 : r' ≤ Params.r1 d)
    (hn16 : 16 * n = 9 * r' * Params.t1 d)
    (hnβ : (n : ℝ) ≤ (Params.q1 d : ℝ) * β) :
    (1 : ℤ) + (Nat.log 2 (Params.t1 d) : ℤ) + (Nat.log 2 r' : ℤ) ≤
      (Dfamily
        (interlaceFun (fun (j : C1 d) (a : R1 d) => M1 d a j) 1)
        (bracketGE (C1 d) (R1 d) 1
          ((2 : ℝ) ^ (-(Params.b1 d : ℝ))) β) : ℤ) := by
  classical
  let x : ℝ := (2 : ℝ) ^ (-(Params.b1 d : ℝ))
  have hxle : x ≤ 1 := by
    dsimp [x]
    have hexp : -(Params.b1 d : ℝ) ≤ (0 : ℝ) := by
      exact neg_nonpos.mpr (by positivity)
    calc (2 : ℝ) ^ (-(Params.b1 d : ℝ))
        ≤ (2 : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 1 := by norm_num
  have hC1card : 1 ≤ Fintype.card (C1 d) := by
    simpa [C1, Fintype.card_fin] using L1_pos d hchk
  unfold Dfamily
  set S : Set ℕ :=
    { m : ℕ | ∃ RC ∈ bracketGE (C1 d) (R1 d) 1 x β,
        m = D (subgame
          (interlaceFun (fun (j : C1 d) (a : R1 d) => M1 d a j) 1)
          RC.1 RC.2) } with hS
  change (1 : ℤ) + (Nat.log 2 (Params.t1 d) : ℤ) + (Nat.log 2 r' : ℤ) ≤
    ((sInf S : ℕ) : ℤ)
  have hSne : S.Nonempty := by
    obtain ⟨RC, hRC⟩ :=
      bracketGE.nonempty (X := C1 d) (Y := R1 d) 1 x β hxle hβle hC1card
    exact ⟨D (subgame
      (interlaceFun (fun (j : C1 d) (a : R1 d) => M1 d a j) 1)
      RC.1 RC.2), RC, hRC, rfl⟩
  have hmem := Nat.sInf_mem hSne
  rcases hmem with ⟨RC, hRC, hRCeq⟩
  rw [hRCeq]
  rcases hRC with ⟨hRows, hCols⟩
  let R' : Finset (R1 d) := RC.2.image (fun c : Fin 1 → R1 d => c 0)
  let C' : Finset (C1 d) := RC.1.image (fun p : Fin 1 × C1 d => p.2)
  let Qall : Finset (Fin (Params.q1 d)) := R'.image (fun a : R1 d => a.1)
  have heval_inj : Function.Injective (fun c : Fin 1 → R1 d => c 0) := by
    intro f g hfg
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    simpa [hi] using hfg
  have hfst_inj : Function.Injective (fun a : R1 d => a.1) := by
    intro a b hab
    exact Prod.ext hab (Subsingleton.elim _ _)
  have hR'card : R'.card = RC.2.card := by
    simpa [R'] using Finset.card_image_of_injective RC.2 heval_inj
  have hQallcard : Qall.card = R'.card := by
    simpa [Qall] using Finset.card_image_of_injective R' hfst_inj
  have hnceil : n ≤
      ⌈((Fintype.card (R1 d) : ℝ) ^ 1) * β⌉₊ := by
    have hx : (n : ℝ) ≤ ((Fintype.card (R1 d) : ℝ) ^ 1) * β := by
      simpa [R1, Fintype.card_prod, Fintype.card_fin] using hnβ
    have hxceil : (n : ℝ) ≤
        (⌈((Fintype.card (R1 d) : ℝ) ^ 1) * β⌉₊ : ℝ) :=
      le_trans hx (Nat.le_ceil _)
    exact_mod_cast hxceil
  have hnQall : n ≤ Qall.card := by
    calc n ≤ ⌈((Fintype.card (R1 d) : ℝ) ^ 1) * β⌉₊ := hnceil
      _ ≤ RC.2.card := hCols
      _ = R'.card := hR'card.symm
      _ = Qall.card := hQallcard.symm
  obtain ⟨Q, hQsub, hQcard'⟩ :=
    Finset.exists_subset_card_eq (s := Qall) hnQall
  have hQcard : 16 * Q.card = 9 * r' * Params.t1 d := by
    rw [hQcard', hn16]
  have hrow : IsEquipartitionedGE
      (R'.image (fun a => ((a.1 : Fin (Params.q1 d)), a.2))) Q 1 := by
    intro q hq
    have hqall : q ∈ Qall := hQsub hq
    rcases Finset.mem_image.mp hqall with ⟨a, haR, hqa⟩
    apply Nat.succ_le_of_lt
    refine Finset.card_pos.mpr ⟨((q : Fin (Params.q1 d)), (0 : Fin 1)), ?_⟩
    simp only [Finset.mem_filter]
    constructor
    · apply Finset.mem_image.mpr
      refine ⟨a, haR, ?_⟩
      exact Prod.ext hqa (Subsingleton.elim _ _)
    · trivial
  have hCimage_inj : Function.Injective (fun p : Fin 1 × C1 d => p.2) := by
    intro a b hab
    exact Prod.ext (Subsingleton.elim _ _) hab
  have hC'card : C'.card = RC.1.card := by
    simpa [C'] using Finset.card_image_of_injective RC.1 hCimage_inj
  have hfilter_card : (RC.1.filter (fun p : Fin 1 × C1 d => p.1 = 0)).card = RC.1.card := by
    have hfilter : RC.1.filter (fun p : Fin 1 × C1 d => p.1 = 0) = RC.1 := by
      ext p
      simp [Subsingleton.elim p.1 0]
    rw [hfilter]
  have hceilC : ⌈(Fintype.card (C1 d) : ℝ) * x⌉₊ ≤ C'.card := by
    calc ⌈(Fintype.card (C1 d) : ℝ) * x⌉₊
        ≤ (RC.1.filter (fun p : Fin 1 × C1 d => p.1 = 0)).card :=
          hRows 0 (by simp)
      _ = RC.1.card := hfilter_card
      _ = C'.card := hC'card.symm
  have hdown_le_x :
      (2 : ℝ) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : ℤ)) ≤ x := by
    dsimp [x]
    rw [← Real.rpow_intCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hsum : (Params.b1 d : ℝ) ≤
        (Params.b1 d + Nat.log 2 (Params.r2 d) : ℝ) := by
      exact_mod_cast Nat.le_add_right (Params.b1 d) (Nat.log 2 (Params.r2 d))
    norm_num
  have hcol : (2 : ℝ) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : ℤ))
        * (Fintype.card (C1 d) : ℝ) ≤ (C'.card : ℝ) := by
    calc (2 : ℝ) ^ (-(Params.b1 d + Nat.log 2 (Params.r2 d) : ℤ))
          * (Fintype.card (C1 d) : ℝ)
        ≤ x * (Fintype.card (C1 d) : ℝ) := by
          exact mul_le_mul_of_nonneg_right hdown_le_x (by positivity)
      _ = (Fintype.card (C1 d) : ℝ) * x := by ring
      _ ≤ (⌈(Fintype.card (C1 d) : ℝ) * x⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (C'.card : ℝ) := by exact_mod_cast hceilC
  have hslice := M1_low_column_stage2 d hd hchk hdiv hTb hRb hgap
    hr'pow hr'1 hr'r1 R' C' Q hQcard hrow hcol
  rw [dfamily_singleton_local] at hslice
  let eRows : {p // p ∈ RC.1} ≃ {j // j ∈ C'} :=
    { toFun := fun p =>
        (⟨p.1.2, by exact Finset.mem_image.mpr ⟨p.1, p.2, rfl⟩⟩ :
          {j // j ∈ C'})
      invFun := fun j =>
        (⟨(0, j.1), by
          rcases Finset.mem_image.mp j.2 with ⟨p, hp, hpj⟩
          have hp0 : p.1 = 0 := Subsingleton.elim p.1 0
          have hp_eq : p = (0, j.1) := by
            exact Prod.ext hp0 (by simpa using hpj)
          simpa [hp_eq] using hp⟩ : {p // p ∈ RC.1})
      left_inv := by
        intro p
        apply Subtype.ext
        exact Prod.ext (Subsingleton.elim _ _) rfl
      right_inv := by
        intro j
        apply Subtype.ext
        rfl }
  let eCols : {c // c ∈ RC.2} ≃ {a // a ∈ R'} :=
    { toFun := fun c =>
        (⟨c.1 0, by exact Finset.mem_image.mpr ⟨c.1, c.2, rfl⟩⟩ :
          {a // a ∈ R'})
      invFun := fun a =>
        (⟨fun _ => a.1, by
          rcases Finset.mem_image.mp a.2 with ⟨c, hc, hca⟩
          have hc_eq : c = fun _ => a.1 := by
            funext i
            have hi : i = 0 := Subsingleton.elim i 0
            simpa [hi] using hca
          simpa [← hc_eq] using hc⟩ : {c // c ∈ RC.2})
      left_inv := by
        intro c
        apply Subtype.ext
        funext i
        have hi : i = 0 := Subsingleton.elim i 0
        simp [hi]
      right_inv := by
        intro a
        apply Subtype.ext
        rfl }
  let fT : {j // j ∈ C'} → {a // a ∈ R'} → Bool :=
    fun j a => M1 d a.1 j.1
  have hgame :
      subgame (interlaceFun (fun (j : C1 d) (a : R1 d) => M1 d a j) 1) RC.1 RC.2 =
        fun p c => fT (eRows p) (eCols c) := by
    funext p c
    have hp0 : (p.1 : Fin 1 × C1 d).1 = 0 := Subsingleton.elim _ _
    simp [subgame, interlaceFun, fT, eRows, eCols, hp0]
  have hDinv := D_equiv_invariance fT eRows eCols
  have hDmember :
      D (subgame (interlaceFun (fun (j : C1 d) (a : R1 d) => M1 d a j) 1)
          RC.1 RC.2) =
        D (subgame (M1 d) R' C') := by
    calc D (subgame (interlaceFun (fun (j : C1 d) (a : R1 d) => M1 d a j) 1)
          RC.1 RC.2)
        = D fT := by rw [hgame]; exact hDinv
      _ = D (subgame (M1 d) R' C') := by
        simpa [fT, subgame] using comp_transpose (subgame (M1 d) R' C')
  rwa [hDmember]

-- CLAIM-BEGIN lem:M1-robust
theorem M1_robust (d : ℕ) (hpow : IsPow2 d)
    (hlog : 256 ≤ Nat.log 2 d) :
    IsRobust (fun (j : C1 d) (a : R1 d) => M1 d a j) Params.delta (Params.b1 d) := by
  classical
  let MT : C1 d → R1 d → Bool := fun j a => M1 d a j
  change IsRobust MT Params.delta (Params.b1 d)
  have hlog64 : 64 ≤ Nat.log 2 d := by omega
  have hd : 2 ≤ d := by
    obtain ⟨k, rfl⟩ := hpow
    have hk : 256 ≤ k := by simpa [log_two_pow] using hlog
    exact Nat.succ_le_of_lt (Nat.one_lt_two_pow (by omega : k ≠ 0))
  have hchk : Params.t1 d ≤ Params.q1 d + 5 :=
    Params.t1_le_q1_add_five hlog64
  obtain ⟨hdiv, hTb, hRb, hgap⟩ := M1_low_column_stage2_gates hpow hlog64
  have hcomp : D (M1 d) = Params.a d + 1 := M1_complexity d hpow hlog64
  have htr : D MT = D (M1 d) := by
    simpa [MT] using comp_transpose (M1 d)
  have hcap := M1_capacity_log_identity d hd hdiv
  have hqpow : Params.q1 d + 2 = 2 ^ Params.a d := (Params.two_pow_a hd).symm
  have hr1pow_some : ∃ k, Params.r1 d = 2 ^ k := by
    have hr1dvd : Params.r1 d ∣ 2 ^ Params.a d := by
      rw [← hqpow]
      exact ⟨Params.t1 d, hdiv⟩
    obtain ⟨j, _hjle, hr1j⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hr1dvd
    exact ⟨j, hr1j⟩
  let Rlog : ℕ := Nat.log 2 (Params.r1 d)
  have hr1pow : Params.r1 d = 2 ^ Rlog := by
    obtain ⟨k, hk⟩ := hr1pow_some
    dsimp [Rlog]
    rw [hk, log_two_pow]
  have hlog1 : 1 ≤ Nat.log 2 d := by omega
  have ht_upper : Params.t1 d ≤ 128 * Nat.log 2 d :=
    (Params.t1_bracket (d := d) hlog1).2
  have hA64 : 64 ≤ Params.r1 d * Params.t1 d := by
    rw [← hdiv]
    have hqlo := Params.le_q1_add_two (d := d) hlog1
    have hsmall : 64 ≤ 2 * Nat.log 2 d ^ 2 := by nlinarith
    omega
  have hr1ge4 : 4 ≤ Params.r1 d := by
    by_contra hlt
    have hr1le3 : Params.r1 d ≤ 3 := by omega
    have hupper : Params.r1 d * Params.t1 d ≤ 3 * (128 * Nat.log 2 d) :=
      Nat.mul_le_mul hr1le3 ht_upper
    have hlower : 2 * Nat.log 2 d ^ 2 ≤ Params.r1 d * Params.t1 d := by
      rw [← hdiv]
      exact Params.le_q1_add_two (d := d) hlog1
    have hkey : 3 * (128 * Nat.log 2 d) < 2 * Nat.log 2 d ^ 2 := by
      nlinarith
    omega
  have hRlog_ge2 : 2 ≤ Rlog := by
    dsimp [Rlog]
    rw [Nat.le_log_iff_pow_le (by norm_num) (by omega : Params.r1 d ≠ 0)]
    norm_num
    exact hr1ge4
  have ht1_clog : Params.t1 d = 2 ^ Nat.clog 2 (64 * Nat.log 2 d) := rfl
  have ht1pow : Params.t1 d = 2 ^ Nat.log 2 (Params.t1 d) := by
    rw [ht1_clog, log_two_pow]
  have ht1ge16 : 16 ≤ Params.t1 d := by
    have ht := (Params.t1_bracket (d := d) hlog1).1
    nlinarith
  have hlogt_ge4 : 4 ≤ Nat.log 2 (Params.t1 d) := by
    calc 4 = Nat.log 2 16 := by norm_num [Nat.log]
      _ ≤ Nat.log 2 (Params.t1 d) := Nat.log_mono_right ht1ge16
  have hdiv16 : 16 ∣ Params.t1 d := by
    rw [show 16 = (2 : Nat) ^ 4 by norm_num, ht1pow]
    exact pow_dvd_pow 2 hlogt_ge4
  have hn_for : ∀ r'' : ℕ, ∃ n : ℕ, 16 * n = 9 * r'' * Params.t1 d := by
    intro r''
    refine ⟨9 * r'' * Params.t1 d / 16, ?_⟩
    have hdiv16prod : 16 ∣ 9 * r'' * Params.t1 d := by
      exact dvd_mul_of_dvd_right hdiv16 (9 * r'')
    rw [mul_comm, Nat.div_mul_cancel hdiv16prod]
  have hqR : (Params.q1 d : ℝ) = (Params.r1 d * Params.t1 d : ℝ) - 2 := by
    have hdivR : ((Params.q1 d + 2 : ℕ) : ℝ) =
        ((Params.r1 d * Params.t1 d : ℕ) : ℝ) := by
      exact_mod_cast hdiv
    norm_num at hdivR ⊢
    linarith
  have hA64R : (64 : ℝ) ≤ (Params.r1 d * Params.t1 d : ℝ) := by
    exact_mod_cast hA64

  obtain ⟨n0, hn0⟩ := hn_for (Params.r1 d)
  have hnβ0 : (n0 : ℝ) ≤ (Params.q1 d : ℝ) * (1 / 2 + Params.delta) := by
    have hn16R : (16 : ℝ) * n0 = 9 * (Params.r1 d * Params.t1 d : ℝ) := by
      exact_mod_cast (by simpa [Nat.mul_assoc] using hn0)
    norm_num [Params.delta]
    nlinarith [hn16R, hqR, hA64R]
  have hfam0 := M1T_family_lower_from_slice d hd hchk hdiv hTb hRb hgap
    (1 / 2 + Params.delta) (by norm_num [Params.delta])
    hr1pow_some (by
      obtain ⟨k, hk⟩ := hr1pow_some
      rw [hk]
      exact Nat.one_le_two_pow)
    (le_refl (Params.r1 d)) hn0 hnβ0

  let rhalf : ℕ := 2 ^ (Rlog - 1)
  have hrhalf_pow : ∃ k, rhalf = 2 ^ k := ⟨Rlog - 1, rfl⟩
  have hrhalf_one : 1 ≤ rhalf := by
    dsimp [rhalf]
    exact Nat.one_le_two_pow
  have hrhalf_le : rhalf ≤ Params.r1 d := by
    dsimp [rhalf]
    rw [hr1pow]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le Rlog 1)
  have h2rhalf : 2 * rhalf = Params.r1 d := by
    dsimp [rhalf]
    rw [hr1pow]
    calc 2 * 2 ^ (Rlog - 1)
        = 2 ^ (Rlog - 1) * 2 := by ring
      _ = 2 ^ ((Rlog - 1) + 1) := by rw [pow_succ]
      _ = 2 ^ Rlog := by congr 1; omega
  have hlog_half : Nat.log 2 rhalf = Rlog - 1 := by
    dsimp [rhalf]
    rw [log_two_pow]
  obtain ⟨n1, hn1⟩ := hn_for rhalf
  have hnβ1 : (n1 : ℝ) ≤ (Params.q1 d : ℝ) * (1 / 4 + Params.delta / 2) := by
    have hn16R : (16 : ℝ) * n1 = 9 * (rhalf : ℝ) * (Params.t1 d : ℝ) := by
      exact_mod_cast hn1
    have h2R : (2 : ℝ) * (rhalf : ℝ) = (Params.r1 d : ℝ) := by
      exact_mod_cast h2rhalf
    have hn32R : (32 : ℝ) * n1 = 9 * (Params.r1 d * Params.t1 d : ℝ) := by
      calc (32 : ℝ) * n1
          = 2 * ((16 : ℝ) * n1) := by ring
        _ = 2 * (9 * (rhalf : ℝ) * (Params.t1 d : ℝ)) := by rw [hn16R]
        _ = 9 * ((2 : ℝ) * rhalf) * (Params.t1 d : ℝ) := by ring
        _ = 9 * (Params.r1 d : ℝ) * (Params.t1 d : ℝ) := by rw [h2R]
        _ = 9 * (Params.r1 d * Params.t1 d : ℝ) := by ring
    norm_num [Params.delta]
    nlinarith [hn32R, hqR, hA64R]
  have hfam1 := M1T_family_lower_from_slice d hd hchk hdiv hTb hRb hgap
    (1 / 4 + Params.delta / 2) (by norm_num [Params.delta])
    hrhalf_pow hrhalf_one hrhalf_le hn1 hnβ1

  let rquarter : ℕ := 2 ^ (Rlog - 2)
  have hrquarter_pow : ∃ k, rquarter = 2 ^ k := ⟨Rlog - 2, rfl⟩
  have hrquarter_one : 1 ≤ rquarter := by
    dsimp [rquarter]
    exact Nat.one_le_two_pow
  have hrquarter_le : rquarter ≤ Params.r1 d := by
    dsimp [rquarter]
    rw [hr1pow]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le Rlog 2)
  have h4rquarter : 4 * rquarter = Params.r1 d := by
    dsimp [rquarter]
    rw [hr1pow]
    calc 4 * 2 ^ (Rlog - 2)
        = 2 ^ 2 * 2 ^ (Rlog - 2) := by norm_num
      _ = 2 ^ (2 + (Rlog - 2)) := by rw [← pow_add]
      _ = 2 ^ Rlog := by congr 1; omega
  have hlog_quarter : Nat.log 2 rquarter = Rlog - 2 := by
    dsimp [rquarter]
    rw [log_two_pow]
  obtain ⟨n2, hn2⟩ := hn_for rquarter
  have hnβ2 : (n2 : ℝ) ≤ (Params.q1 d : ℝ) * (1 / 8 + Params.delta / 4) := by
    have hn16R : (16 : ℝ) * n2 = 9 * (rquarter : ℝ) * (Params.t1 d : ℝ) := by
      exact_mod_cast hn2
    have h4R : (4 : ℝ) * (rquarter : ℝ) = (Params.r1 d : ℝ) := by
      exact_mod_cast h4rquarter
    have hn64R : (64 : ℝ) * n2 = 9 * (Params.r1 d * Params.t1 d : ℝ) := by
      calc (64 : ℝ) * n2
          = 4 * ((16 : ℝ) * n2) := by ring
        _ = 4 * (9 * (rquarter : ℝ) * (Params.t1 d : ℝ)) := by rw [hn16R]
        _ = 9 * ((4 : ℝ) * rquarter) * (Params.t1 d : ℝ) := by ring
        _ = 9 * (Params.r1 d : ℝ) * (Params.t1 d : ℝ) := by rw [h4R]
        _ = 9 * (Params.r1 d * Params.t1 d : ℝ) := by ring
    norm_num [Params.delta]
    nlinarith [hn64R, hqR, hA64R]
  have hfam2 := M1T_family_lower_from_slice d hd hchk hdiv hTb hRb hgap
    (1 / 8 + Params.delta / 4) (by norm_num [Params.delta])
    hrquarter_pow hrquarter_one hrquarter_le hn2 hnβ2

  unfold IsRobust
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [htr, hcomp]
    omega
  · have hDle : (D MT : ℤ) ≤
        (Dfamily (interlaceFun MT 1)
          (bracketGE (C1 d) (R1 d) 1 ((2 : ℝ) ^ (-(Params.b1 d : ℝ)))
            (1 / 2 + Params.delta)) : ℤ) := by
      rw [htr, hcomp]
      calc ((Params.a d + 1 : ℕ) : ℤ)
          = (1 : ℤ) + (Nat.log 2 (Params.t1 d) : ℤ)
              + (Nat.log 2 (Params.r1 d) : ℤ) := by
              rw [hcap]
              omega
        _ ≤ (Dfamily (interlaceFun MT 1)
          (bracketGE (C1 d) (R1 d) 1 ((2 : ℝ) ^ (-(Params.b1 d : ℝ)))
            (1 / 2 + Params.delta)) : ℤ) := by
              simpa [MT, Rlog] using hfam0
    exact_mod_cast hDle
  · rw [htr, hcomp]
    calc (((Params.a d + 1 : ℕ) : ℤ) - 2)
        = (1 : ℤ) + (Nat.log 2 (Params.t1 d) : ℤ) + (Nat.log 2 rquarter : ℤ) := by
            rw [hcap, hlog_quarter]
            dsimp [Rlog] at hRlog_ge2
            omega
      _ ≤ (Dfamily (interlaceFun MT 1)
          (bracketGE (C1 d) (R1 d) 1 ((2 : ℝ) ^ (-(Params.b1 d : ℝ)))
            (1 / 8 + Params.delta / 4)) : ℤ) := by
            simpa [MT] using hfam2
  · rw [htr, hcomp]
    calc (((Params.a d + 1 : ℕ) : ℤ) - 1)
        = (1 : ℤ) + (Nat.log 2 (Params.t1 d) : ℤ) + (Nat.log 2 rhalf : ℤ) := by
            rw [hcap, hlog_half]
            dsimp [Rlog] at hRlog_ge2
            omega
      _ ≤ (Dfamily (interlaceFun MT 1)
          (bracketGE (C1 d) (R1 d) 1 ((2 : ℝ) ^ (-(Params.b1 d : ℝ)))
            (1 / 4 + Params.delta / 2)) : ℤ) := by
            simpa [MT] using hfam1
-- CLAIM-END lem:M1-robust

end M1Robust
end NPCC
