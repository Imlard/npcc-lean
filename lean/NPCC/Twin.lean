import Mathlib
import NPCC.Bridge
import NPCC.Complexity
import Workspace.Types.MatComplexity

/-! # Value-level correspondence with the reused interlace library
Digit-encoded column flattening, and the transfer inequality that puts the
verified artifact's entire bracket engine behind the typed definitions. -/

namespace NPCC

open Workspace.Types.CommComplexity Workspace.Types.Interlace
open Workspace.Types.MatComplexity Workspace.Types.Bracket
open Workspace.Types.Extract Workspace.Types.BoolMat
open Workspace.Types.Protocol

-- CLAIM-BEGIN def:encCol
/-- Digit flattening of a typed interlace column: the tuple `c : Fin p → Fin n`
becomes the base-`n` numeral `Σ γ, c γ · n^γ`. The artifact's interlace reads
column `j`'s digit `γ` as `(j / n^γ) % n` (`Workspace.Types.Interlace`);
`encCol` is the inverse presentation, pairing with `encRow` (`NPCC.Bridge`)
to flatten typed extraction data to artifact extraction data. -/
def encCol {p n : ℕ} (c : Fin p → Fin n) : ℕ :=
  ∑ γ : Fin p, (c γ : ℕ) * n ^ (γ : ℕ)
-- CLAIM-END def:encCol

theorem encCol_succ {p n : ℕ} (c : Fin (p+1) → Fin n) :
    encCol c = (c 0 : ℕ) + n * encCol (fun γ : Fin p => c γ.succ) := by
  unfold encCol
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
  rw [Finset.mul_sum]; congr 1
  apply Finset.sum_congr rfl; intro γ _; ring

-- CLAIM-BEGIN lem:digit-extract
/-- The base-`n` digit laws for `encCol`: the numeral is below `n^p`, and
extracting digit `q` the artifact's way recovers the tuple entry. (Injectivity
of `encCol` follows and lives as a companion lemma below.) -/
theorem encCol_digit {p n : ℕ} (hn : 0 < n) (c : Fin p → Fin n) :
    encCol c < n ^ p ∧
    ∀ q : Fin p, (encCol c / n ^ (q : ℕ)) % n = (c q : ℕ) :=
-- CLAIM-END lem:digit-extract
  by
  induction p with
  | zero => exact ⟨by simp [encCol], fun q => absurd q.isLt (Nat.not_lt_zero _)⟩
  | succ p ih =>
    have hc0 : (c 0 : ℕ) < n := (c 0).isLt
    set tail : Fin p → Fin n := fun γ => c γ.succ with htail
    obtain ⟨ihlt, ihdig⟩ := ih tail
    have hrec : encCol c = (c 0 : ℕ) + n * encCol tail := encCol_succ c
    refine ⟨?_, ?_⟩
    · rw [hrec]
      have hb : n * encCol tail + n ≤ n ^ (p+1) := by
        have h1 : encCol tail + 1 ≤ n ^ p := ihlt
        calc n * encCol tail + n = n * (encCol tail + 1) := by ring
          _ ≤ n * n ^ p := by exact Nat.mul_le_mul_left n h1
          _ = n ^ (p+1) := by rw [pow_succ]; ring
      omega
    · intro q
      refine Fin.cases ?_ ?_ q
      · simp only [Fin.val_zero, pow_zero, Nat.div_one]
        rw [hrec, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc0]
      · intro q'
        simp only [Fin.val_succ, pow_succ]
        rw [hrec, mul_comm (n ^ (q' : ℕ)) n, ← Nat.div_div_eq_div_mul]
        rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hc0, Nat.zero_add]
        exact ihdig q'

theorem encCol_injective {p n : ℕ} (hn : 0 < n) :
    Function.Injective (encCol (p := p) (n := n)) := by
  intro c d hcd; funext q; apply Fin.ext
  have h1 := (encCol_digit hn c).2 q
  have h2 := (encCol_digit hn d).2 q
  rw [hcd] at h1; rw [h1] at h2; exact h2

/-! ## Interlace entry decode -/

theorem interlace_entry_enc {M : BoolMat} {p : ℕ}
    (hm : 0 < M.m) (hn : 0 < M.n)
    (a : Fin p × Fin M.m) (c : Fin p → Fin M.n)
    (hi : encRow a < (interlace M p).m) (hj : encCol c < (interlace M p).n) :
    (interlace M p).e ⟨encRow a, hi⟩ ⟨encCol c, hj⟩ = M.e a.2 (c a.1) := by
  have hrowdiv : encRow a / M.m = (a.1 : ℕ) := by
    unfold encRow
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt a.2.isLt, Nat.zero_add]
  have hrowmod : encRow a % M.m = (a.2 : ℕ) := by
    unfold encRow
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.2.isLt]
  simp only [Workspace.Types.Interlace.interlace]
  congr 1
  · apply Fin.ext; simpa using hrowmod
  · apply Fin.ext
    change encCol c / M.n ^ (encRow a / M.m) % M.n = (c a.1 : ℕ)
    rw [hrowdiv]
    exact (encCol_digit hn c).2 a.1

/-! ## Subgame monotonicity under trimming -/

open Workspace.Types.Protocol

def Protocol.mapNodes {A B A' B' Z : Type*} (ρ : A' → A) (σ : B' → B) :
    Protocol A B Z → Protocol A' B' Z
  | Protocol.leaf z => Protocol.leaf z
  | Protocol.aNode a l r =>
      Protocol.aNode (fun x => a (ρ x)) (Protocol.mapNodes ρ σ l) (Protocol.mapNodes ρ σ r)
  | Protocol.bNode b l r =>
      Protocol.bNode (fun y => b (σ y)) (Protocol.mapNodes ρ σ l) (Protocol.mapNodes ρ σ r)

theorem Protocol.cost_mapNodes {A B A' B' Z : Type*} (ρ : A' → A) (σ : B' → B)
    (P : Protocol A B Z) : (Protocol.mapNodes ρ σ P).cost = P.cost := by
  induction P with
  | leaf z => rfl
  | aNode a l r ihl ihr => simp only [Protocol.mapNodes, Protocol.cost, ihl, ihr]
  | bNode b l r ihl ihr => simp only [Protocol.mapNodes, Protocol.cost, ihl, ihr]

theorem Protocol.eval_mapNodes {A B A' B' Z : Type*} (ρ : A' → A) (σ : B' → B)
    (P : Protocol A B Z) (x : A') (y : B') :
    (Protocol.mapNodes ρ σ P).eval x y = P.eval (ρ x) (σ y) := by
  induction P generalizing x y with
  | leaf z => rfl
  | aNode a l r ihl ihr => simp only [Protocol.mapNodes, Protocol.eval, ihl, ihr]
  | bNode b l r ihl ihr => simp only [Protocol.mapNodes, Protocol.eval, ihl, ihr]

theorem achievableCosts_mapNodes {A B A' B' Z : Type*}
    (f : A → B → Z) (ρ : A' → A) (σ : B' → B) :
    AchievableCosts f ⊆ AchievableCosts (fun a b => f (ρ a) (σ b)) := by
  rintro c ⟨P, hcost, hcomp⟩
  refine ⟨Protocol.mapNodes ρ σ P, ?_, ?_⟩
  · rw [Protocol.cost_mapNodes]; exact hcost
  · intro x y; rw [Protocol.eval_mapNodes]; exact hcomp (ρ x) (σ y)

theorem D_mapNodes_le {A B A' B' Z : Type*} [Nonempty Z]
    [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
    (f : A → B → Z) (ρ : A' → A) (σ : B' → B) :
    D (fun a b => f (ρ a) (σ b)) ≤ D f := by
  have hne : (AchievableCosts f).Nonempty := Workspace.UpperBound.AchievableCosts_nonempty f
  have hmem : D f ∈ AchievableCosts f := by
    have := Nat.sInf_mem hne; simpa [D] using this
  have hmem' := achievableCosts_mapNodes f ρ σ hmem
  have := Nat.sInf_le hmem'; simpa [D] using this

theorem D_subgame_mono {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B → Bool) {R0 R : Finset A} {C0 C : Finset B}
    (hR : R0 ⊆ R) (hC : C0 ⊆ C) :
    D (subgame f R0 C0) ≤ D (subgame f R C) := by
  let ρ : {a // a ∈ R0} → {a // a ∈ R} := fun a => ⟨a.1, hR a.2⟩
  let σ : {c // c ∈ C0} → {c // c ∈ C} := fun c => ⟨c.1, hC c.2⟩
  have heq : subgame f R0 C0 =
      (fun (a : {a // a ∈ R0}) (c : {c // c ∈ C0}) => (subgame f R C) (ρ a) (σ c)) := by
    funext a c; rfl
  rw [heq]; exact D_mapNodes_le (subgame f R C) ρ σ

/-! ## Sorted-order flattening equivalence -/

noncomputable def flatEquiv {A : Type*} (R0 : Finset A) (g : A → ℕ)
    (hg : Set.InjOn g R0) :
    {a // a ∈ R0} ≃ Fin (R0.image g).card :=
  (Equiv.ofBijective
    (fun a : {a // a ∈ R0} =>
      (⟨g a.1, Finset.mem_image.mpr ⟨a.1, a.2, rfl⟩⟩ : {b // b ∈ R0.image g}))
    (by
      constructor
      · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
        have : g a = g b := by simpa using hab
        exact Subtype.ext (hg ha hb this)
      · rintro ⟨b, hb⟩
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
        exact ⟨⟨a, ha⟩, rfl⟩)).trans
  ((R0.image g).orderIsoOfFin rfl).symm.toEquiv

theorem flatEquiv_getD {A : Type*} (R0 : Finset A) (g : A → ℕ)
    (hg : Set.InjOn g R0) (a : {a // a ∈ R0}) :
    ((R0.image g).sort (· ≤ ·)).getD (flatEquiv R0 g hg a) 0 = g a.1 := by
  have hmem : g a.1 ∈ R0.image g := Finset.mem_image.mpr ⟨a.1, a.2, rfl⟩
  have hfe : flatEquiv R0 g hg a = ((R0.image g).orderIsoOfFin rfl).symm ⟨g a.1, hmem⟩ := by
    unfold flatEquiv; rfl
  have hemb : (R0.image g).orderEmbOfFin rfl (flatEquiv R0 g hg a) = g a.1 := by
    rw [hfe, ← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  rw [Finset.orderEmbOfFin_apply] at hemb
  rw [List.getD_eq_getElem _ _ (by rw [Finset.length_sort]; exact (flatEquiv R0 g hg a).2)]
  exact hemb

/-! ## Abstract value isomorphism -/

theorem Dmat_extract_eq_Dsubgame
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (F : A → B → Bool) (G : BoolMat)
    (R0 : Finset A) (C0 : Finset B)
    (rowEnc : A → ℕ) (colEnc : B → ℕ)
    (hrow : Set.InjOn rowEnc R0) (hcol : Set.InjOn colEnc C0)
    (hentry : ∀ (a : {a // a ∈ R0}) (c : {c // c ∈ C0})
        (hi : ((R0.image rowEnc).sort (· ≤ ·)).getD (flatEquiv R0 rowEnc hrow a) 0 < G.m)
        (hj : ((C0.image colEnc).sort (· ≤ ·)).getD (flatEquiv C0 colEnc hcol c) 0 < G.n),
        G.e ⟨_, hi⟩ ⟨_, hj⟩ = F a.1 c.1)
    (hbound_r : ∀ (a : {a // a ∈ R0}),
        ((R0.image rowEnc).sort (· ≤ ·)).getD (flatEquiv R0 rowEnc hrow a) 0 < G.m)
    (hbound_c : ∀ (c : {c // c ∈ C0}),
        ((C0.image colEnc).sort (· ≤ ·)).getD (flatEquiv C0 colEnc hcol c) 0 < G.n) :
    Dmat (extract G (R0.image rowEnc) (C0.image colEnc))
      = D (subgame F R0 C0) := by
  set Rf := R0.image rowEnc with hRf
  set Cf := C0.image colEnc with hCf
  let e1 : {a // a ∈ R0} ≃ Fin (extract G Rf Cf).m :=
    (flatEquiv R0 rowEnc hrow).trans (finCongr (by rw [extract_m])).symm
  let e2 : {c // c ∈ C0} ≃ Fin (extract G Rf Cf).n :=
    (flatEquiv C0 colEnc hcol).trans (finCongr (by rw [extract_n])).symm
  have hval : subgame F R0 C0 = (fun a c => (extract G Rf Cf).e (e1 a) (e2 c)) := by
    funext a c
    show F a.1 c.1 = (extract G Rf Cf).e (e1 a) (e2 c)
    have hi : (Rf.sort (· ≤ ·)).getD ((flatEquiv R0 rowEnc hrow a : Fin _) : ℕ) 0 < G.m :=
      hbound_r a
    have hj : (Cf.sort (· ≤ ·)).getD ((flatEquiv C0 colEnc hcol c : Fin _) : ℕ) 0 < G.n :=
      hbound_c c
    show F a.1 c.1 =
      (if h : (Rf.sort (· ≤ ·)).getD ((flatEquiv R0 rowEnc hrow a : Fin _) : ℕ) 0 < G.m
              ∧ (Cf.sort (· ≤ ·)).getD ((flatEquiv C0 colEnc hcol c : Fin _) : ℕ) 0 < G.n
        then G.e ⟨_, h.1⟩ ⟨_, h.2⟩ else false)
    rw [dif_pos ⟨hi, hj⟩]
    exact (hentry a c hi hj).symm
  rw [hval]
  exact (D_equiv_invariance (extract G Rf Cf).e e1 e2).symm

theorem twin_degenerate_Mn {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (M : BoolMat)
    (eX : Fin M.m ≃ X) (eY : Fin M.n ≃ Y)
    (_he : ∀ i j, M.e i j = f (eX i) (eY j))
    {p : ℕ} {x y : ℝ} (_hx0 : 0 < x) (_hx1 : x ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (_hX : 1 ≤ Fintype.card X)
    (hmX : M.m = Fintype.card X) (hnY : M.n = Fintype.card Y) (_hmpos : 0 < M.m)
    (hn0 : M.n = 0)
    (R : Finset (Fin p × X)) (C : Finset (Fin p → Y))
    (hrowGE : IsEquipartitionedGE R (Finset.univ : Finset (Fin p))
      ⌈(Fintype.card X : ℝ) * x⌉₊)
    (hcolGE : ⌈((Fintype.card Y : ℝ) ^ p) * y⌉₊ ≤ C.card) :
    DSet (bracket M p x y) ≤ D (subgame (interlaceFun f p) R C) := by
  classical
  -- D-value zero whenever a party's input type is empty.
  have hDzero : ∀ {A B : Type} [Fintype A] [Fintype B] (g : A → B → Bool),
      (IsEmpty A ∨ IsEmpty B) → D g = 0 := by
    intro A B _ _ g hAB
    have hmem : (0 : ℕ) ∈ AchievableCosts g := by
      refine ⟨Workspace.Types.Protocol.Protocol.leaf false, rfl, ?_⟩
      intro a b
      rcases hAB with h | h
      · exact (h.false a).elim
      · exact (h.false b).elim
    have := Nat.sInf_le hmem
    simpa [D] using Nat.le_zero.mp this
  -- Suffices DSet (bracket M p x y) = 0.
  suffices hDS : DSet (bracket M p x y) = 0 by rw [hDS]; exact Nat.zero_le _
  -- exhibit a bracket member g with a degenerate dimension.
  rcases Nat.eq_zero_or_pos p with hp0 | hppos
  · -- p = 0 : interlace has 0 rows; member R=∅, C={0}.
    subst hp0
    have hyceil : (⌈((M.n ^ 0 : ℕ) : ℝ) * y⌉₊) = 1 := by
      simp only [pow_zero, Nat.cast_one, one_mul]
      have : ⌈y⌉₊ = 1 := by
        rw [Nat.ceil_eq_iff (by norm_num)]
        exact ⟨by simpa using hy0, by simpa using hy1⟩
      exact this
    -- bracket member: R = ∅, C = {0}
    have hmemM : extract (interlace M 0) ∅ {0} ∈ bracket M 0 x y := by
      refine ⟨∅, {0}, ?_, ?_, ?_, ?_, rfl⟩
      · simp
      · intro γ hγ; exact absurd hγ (Nat.not_lt_zero _)
      · intro c hc
        rw [Finset.mem_singleton] at hc; subst hc
        simp
      · rw [Finset.card_singleton, hyceil]
    have hgm : (extract (interlace M 0) ∅ {0}).m = 0 := by rw [extract_m]; rfl
    have hDmatg : Dmat (extract (interlace M 0) ∅ {0}) = 0 := by
      have hem : IsEmpty (Fin (extract (interlace M 0) ∅ {0}).m) := by
        rw [hgm]; exact Fin.isEmpty
      exact hDzero (extract (interlace M 0) ∅ {0}).e (Or.inl hem)
    apply Nat.le_zero.mp
    apply Nat.sInf_le
    exact ⟨_, hmemM, hDmatg⟩
  · -- p ≥ 1 and M.n = 0 : every column set is empty; member has 0 columns.
    -- bracket is nonempty via bridge_bracket from a bracketGE member.
    have hcardY0 : Fintype.card Y = 0 := by rw [← hnY]; exact hn0
    have hcardYp : Fintype.card Y ^ p = 0 := by rw [hcardY0]; exact Nat.zero_pow hppos
    -- The member (∅ columns): use the caller's R,C flattened by bridge_bracket.
    obtain ⟨Rf, Cf, hRfsub, hRfequi, hCfsub, hCfcard, hmemMat⟩ :=
      bridge_bracket (X := X) (Y := Y) (p := p) (x := x) (y := y) (R, C) ⟨hrowGE, hcolGE⟩
    have hmemM := hmemMat M hmX hnY
    -- Cf ⊆ range (card Y ^ p) = range 0 = ∅, so Cf = ∅.
    have hCfempty : Cf = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro c hc
      have hcr := hCfsub hc
      rw [hcardYp] at hcr
      exact absurd hcr (by simp)
    -- g = extract (interlace M p) Rf Cf has 0 columns
    have hgn : (extract (interlace M p) Rf Cf).n = 0 := by
      rw [extract_n, hCfempty]; rfl
    have hDmatg : Dmat (extract (interlace M p) Rf Cf) = 0 := by
      have hem : IsEmpty (Fin (extract (interlace M p) Rf Cf).n) := by
        rw [hgn]; exact Fin.isEmpty
      exact hDzero (extract (interlace M p) Rf Cf).e (Or.inr hem)
    -- DSet ≤ 0
    apply Nat.le_zero.mp
    apply Nat.sInf_le
    exact ⟨_, hmemM, hDmatg⟩

theorem DSet_le_Dfamily_impl {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (M : BoolMat)
    (eX : Fin M.m ≃ X) (eY : Fin M.n ≃ Y)
    (he : ∀ i j, M.e i j = f (eX i) (eY j))
    {p : ℕ} {x y : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hX : 1 ≤ Fintype.card X) :
    DSet (bracket M p x y)
      ≤ Dfamily (interlaceFun f p) (bracketGE X Y p x y) := by
  classical
  -- card identifications
  have hmX : M.m = Fintype.card X := by
    have := Fintype.card_congr eX; rwa [Fintype.card_fin] at this
  have hnY : M.n = Fintype.card Y := by
    have := Fintype.card_congr eY; rwa [Fintype.card_fin] at this
  have hmpos : 0 < M.m := by rw [hmX]; exact hX
  -- Dfamily member extraction
  have hne : (bracketGE X Y p x y).Nonempty := bracketGE.nonempty p x y hx1 hy1 hX
  have hsetne : { d : ℕ | ∃ RC ∈ bracketGE X Y p x y,
      d = D (subgame (interlaceFun f p) RC.1 RC.2) }.Nonempty := by
    obtain ⟨RC, hRC⟩ := hne
    exact ⟨_, RC, hRC, rfl⟩
  have hmem := Nat.sInf_mem hsetne
  obtain ⟨RC, hRCmem, hRCeq⟩ := hmem
  -- so Dfamily = D (subgame ... RC.1 RC.2)
  have hDfam : Dfamily (interlaceFun f p) (bracketGE X Y p x y)
      = D (subgame (interlaceFun f p) RC.1 RC.2) := hRCeq
  rw [hDfam]
  set R := RC.1 with hRdef
  set C := RC.2 with hCdef
  obtain ⟨hrowGE, hcolGE⟩ := hRCmem
  -- Handle M.n = 0 (Y empty) separately; main content is 0 < M.n.
  rcases Nat.eq_zero_or_pos M.n with hn0 | hnpos
  · -- degenerate: bracket columns live in range (M.n^p); DSet collapses.
    exact twin_degenerate_Mn f M eX eY he hx0 hx1 hy0 hy1 hX hmX hnY hmpos hn0
      R C hrowGE hcolGE
  -- MAIN CASE: 0 < M.n.
  set K := ⌈(Fintype.card X : ℝ) * x⌉₊ with hKdef
  set S := ⌈(Fintype.card Y : ℝ) ^ p * y⌉₊ with hSdef
  -- Trim columns: C0 ⊆ C with |C0| = S.
  have hScard : S ≤ C.card := by
    rw [hSdef]; exact hcolGE
  obtain ⟨C0, hC0sub, hC0card⟩ := Finset.exists_subset_card_eq hScard
  -- Trim rows per fiber to exactly K.
  have hch : ∀ q : Fin p, ∃ t ⊆ R.filter (fun a => a.1 = q), t.card = K :=
    fun q => Finset.exists_subset_card_eq (hrowGE q (Finset.mem_univ q))
  choose t hts htcard using hch
  set R0 := Finset.univ.biUnion (fun q : Fin p => t q) with hR0def
  have htsub : ∀ q, t q ⊆ R := fun q => (hts q).trans (Finset.filter_subset _ _)
  have hR0sub : R0 ⊆ R := by
    rw [hR0def]; intro a ha
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at ha
    obtain ⟨q, hq⟩ := ha; exact htsub q hq
  -- flattening functions
  set rowEnc : (Fin p × X) → ℕ := fun a => encRow (a.1, eX.symm a.2) with hrowEnc
  set colEnc : (Fin p → Y) → ℕ := fun c => encCol (fun γ => eY.symm (c γ)) with hcolEnc
  -- injectivity of rowEnc, colEnc (globally injective, hence InjOn)
  have hrowInj : Function.Injective rowEnc := by
    intro a b hab
    rw [hrowEnc] at hab
    have := encRow_injective hab
    have h1 : a.1 = b.1 := (Prod.ext_iff.mp this).1
    have h2 : eX.symm a.2 = eX.symm b.2 := (Prod.ext_iff.mp this).2
    exact Prod.ext h1 (eX.symm.injective h2)
  have hcolInj : Function.Injective colEnc := by
    intro c d hcd
    rw [hcolEnc] at hcd
    have := encCol_injective hnpos hcd
    funext γ
    have := congrFun this γ
    exact eY.symm.injective this
  have hrowIO : Set.InjOn rowEnc R0 := hrowInj.injOn
  have hcolIO : Set.InjOn colEnc C0 := hcolInj.injOn
  -- The flattened sets
  set Rflat := R0.image rowEnc with hRflat
  set Cflat := C0.image colEnc with hCflat
  -- dimension facts of the interlace
  have hIm : (interlace M p).m = M.m * p := rfl
  have hIn : (interlace M p).n = M.n ^ p := rfl
  -- rowEnc bound (all a): rowEnc a < M.m * p, given p arises from a.1 < p
  have hrowbd : ∀ a : Fin p × X, rowEnc a < M.m * p := by
    intro a
    rw [hrowEnc]
    have hlt : (a.1 : ℕ) < p := a.1.isLt
    have h2 : (eX.symm a.2 : ℕ) < M.m := (eX.symm a.2).isLt
    have : encRow (a.1, eX.symm a.2) < M.m * ((a.1 : ℕ) + 1) := by
      unfold encRow
      have : M.m * ((a.1 : ℕ) + 1) = M.m * (a.1 : ℕ) + M.m := by ring
      rw [this]; simp only; omega
    calc encRow (a.1, eX.symm a.2) < M.m * ((a.1 : ℕ) + 1) := this
      _ ≤ M.m * p := Nat.mul_le_mul_left M.m hlt
  -- colEnc bound: colEnc c < M.n^p
  have hcolbd : ∀ c : Fin p → Y, colEnc c < M.n ^ p := by
    intro c; rw [hcolEnc]; exact (encCol_digit hnpos _).1
  -- value-iso pointwise ingredients ---------------------------------------
  -- bounds in the flatEquiv-getD form required by Dmat_extract_eq_Dsubgame
  have hbnd_r : ∀ a : {a // a ∈ R0},
      (Rflat.sort (· ≤ ·)).getD (flatEquiv R0 rowEnc hrowIO a) 0 < (interlace M p).m := by
    intro a
    rw [flatEquiv_getD R0 rowEnc hrowIO a, hIm]
    exact hrowbd a.1
  have hbnd_c : ∀ c : {c // c ∈ C0},
      (Cflat.sort (· ≤ ·)).getD (flatEquiv C0 colEnc hcolIO c) 0 < (interlace M p).n := by
    intro c
    rw [flatEquiv_getD C0 colEnc hcolIO c, hIn]
    exact hcolbd c.1
  -- entry match
  have hentry : ∀ (a : {a // a ∈ R0}) (c : {c // c ∈ C0})
      (hi : (Rflat.sort (· ≤ ·)).getD (flatEquiv R0 rowEnc hrowIO a) 0 < (interlace M p).m)
      (hj : (Cflat.sort (· ≤ ·)).getD (flatEquiv C0 colEnc hcolIO c) 0 < (interlace M p).n),
      (interlace M p).e ⟨_, hi⟩ ⟨_, hj⟩ = interlaceFun f p a.1 c.1 := by
    intro a c hi hj
    -- rewrite the getD positions to rowEnc/colEnc
    have hrE := flatEquiv_getD R0 rowEnc hrowIO a
    have hcE := flatEquiv_getD C0 colEnc hcolIO c
    -- decode via interlace_entry_enc
    have hi' : encRow (a.1.1, eX.symm a.1.2) < (interlace M p).m := by
      rw [hIm]; exact hrowbd a.1
    have hj' : encCol (fun γ => eY.symm (a.1.1 |> fun _ => c.1 γ)) < (interlace M p).n := by
      rw [hIn]; exact hcolbd c.1
    -- The concrete decode: interlace entry at (encRow ..)(encCol ..) = M.e (eX.symm a.1.2) ((..) a.1.1)
    have hdec := interlace_entry_enc (M := M) (p := p) hmpos hnpos
      (a.1.1, eX.symm a.1.2) (fun γ => eY.symm (c.1 γ)) hi' hj'
    -- LHS entry at getD-positions equals entry at (encRow ..)(encCol ..) via congr on positions
    have hpos_r : (Rflat.sort (· ≤ ·)).getD (flatEquiv R0 rowEnc hrowIO a) 0
        = encRow (a.1.1, eX.symm a.1.2) := hrE.trans (congrFun hrowEnc a.1)
    have hpos_c : (Cflat.sort (· ≤ ·)).getD (flatEquiv C0 colEnc hcolIO c) 0
        = encCol (fun γ => eY.symm (c.1 γ)) := hcE.trans (congrFun hcolEnc c.1)
    -- assemble
    have hlhs : (interlace M p).e ⟨_, hi⟩ ⟨_, hj⟩
        = (interlace M p).e ⟨encRow (a.1.1, eX.symm a.1.2), hi'⟩
            ⟨encCol (fun γ => eY.symm (c.1 γ)), hj'⟩ := by
      congr 1 <;> [exact Fin.ext hpos_r; exact Fin.ext hpos_c]
    rw [hlhs, hdec]
    -- M.e (eX.symm a.1.2) ((fun γ => eY.symm (c.1 γ)) a.1.1) = f a.1.2 (c.1 a.1.1)
    show M.e (eX.symm a.1.2) (eY.symm (c.1 a.1.1)) = f a.1.2 (c.1 a.1.1)
    rw [he]
    simp only [Equiv.apply_symm_apply]
  -- Value isomorphism
  have hviso : Dmat (extract (interlace M p) Rflat Cflat)
      = D (subgame (interlaceFun f p) R0 C0) := by
    rw [hRflat, hCflat]
    exact Dmat_extract_eq_Dsubgame (interlaceFun f p) (interlace M p) R0 C0
      rowEnc colEnc hrowIO hcolIO hentry hbnd_r hbnd_c
  -- bracket membership of extract Rflat Cflat
  have hbracket_mem : extract (interlace M p) Rflat Cflat ∈ bracket M p x y := by
    refine ⟨Rflat, Cflat, ?_, ?_, ?_, ?_, rfl⟩
    · -- Rflat ⊆ range (M.m * p)
      intro j hj
      rw [hRflat] at hj
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_range.mpr (hrowbd a)
    · -- IsEquipartitioned Rflat M.m ((M.m:ℝ)*x) p
      intro γ hγ
      -- rewrite the ceil target ⌈(M.m:ℝ)*x⌉₊ = K
      have hceilK : ⌈(M.m : ℝ) * x⌉₊ = K := by rw [hKdef, hmX]
      rw [hceilK]
      -- filter of Rflat to block γ = image rowEnc of (t ⟨γ,hγ⟩)
      have hfilter :
          (Rflat.filter (fun i => M.m * γ ≤ i ∧ i < M.m * (γ + 1)))
            = (t ⟨γ, hγ⟩).image rowEnc := by
        ext j
        constructor
        · intro hj
          rw [Finset.mem_filter] at hj
          obtain ⟨hjR, hblock⟩ := hj
          rw [hRflat, Finset.mem_image] at hjR
          obtain ⟨a, haR0, rfl⟩ := hjR
          rw [hR0def, Finset.mem_biUnion] at haR0
          obtain ⟨q, _, hat⟩ := haR0
          have haq : a.1 = q := (Finset.mem_filter.mp (hts q hat)).2
          have hbi : ((a.1 : ℕ)) = γ := by
            apply (encRow_block_iff (m := M.m) (a.1, eX.symm a.2) γ).mp
            rw [hrowEnc] at hblock; exact hblock
          have hqγ : q = (⟨γ, hγ⟩ : Fin p) := by
            apply Fin.ext; rw [← haq]; exact hbi
          exact Finset.mem_image.mpr ⟨a, by rw [← hqγ]; exact hat, rfl⟩
        · intro hj
          rw [Finset.mem_image] at hj
          obtain ⟨a, hat, rfl⟩ := hj
          have haq : a.1 = (⟨γ, hγ⟩ : Fin p) :=
            (Finset.mem_filter.mp (hts _ hat)).2
          have hbi : ((a.1 : ℕ)) = γ := by rw [haq]
          rw [Finset.mem_filter]
          refine ⟨?_, ?_⟩
          · rw [hRflat, Finset.mem_image]
            exact ⟨a, by rw [hR0def]; exact Finset.mem_biUnion.mpr ⟨⟨γ, hγ⟩, Finset.mem_univ _, hat⟩, rfl⟩
          · rw [hrowEnc]
            exact (encRow_block_iff (m := M.m) (a.1, eX.symm a.2) γ).mpr hbi
      rw [hfilter, Finset.card_image_of_injOn (hrowInj.injOn), htcard ⟨γ, hγ⟩]
    · -- Cflat ⊆ range (M.n ^ p)
      intro j hj
      rw [hCflat] at hj
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_range.mpr (hcolbd c)
    · -- Cflat.card = ⌈(M.n^p : ℕ) * y⌉₊
      rw [hCflat, Finset.card_image_of_injOn hcolIO, hC0card, hSdef]
      rw [show ((M.n ^ p : ℕ) : ℝ) = (Fintype.card Y : ℝ) ^ p by rw [hnY]; push_cast; ring]
  -- DSet ≤ Dmat (extract ...)
  have hDSet_le : DSet (bracket M p x y) ≤ Dmat (extract (interlace M p) Rflat Cflat) := by
    apply Nat.sInf_le
    exact ⟨extract (interlace M p) Rflat Cflat, hbracket_mem, rfl⟩
  -- mono
  have hmono : D (subgame (interlaceFun f p) R0 C0)
      ≤ D (subgame (interlaceFun f p) R C) :=
    D_subgame_mono (interlaceFun f p) hR0sub hC0sub
  calc DSet (bracket M p x y)
      ≤ Dmat (extract (interlace M p) Rflat Cflat) := hDSet_le
    _ = D (subgame (interlaceFun f p) R0 C0) := hviso
    _ ≤ D (subgame (interlaceFun f p) R C) := hmono


-- CLAIM-BEGIN lem:DSet-le-Dfamily
/-- THE VALUE-LEVEL TRANSFER. For a typed game `f` and any `BoolMat` `M`
presenting the same matrix through row/column identifications
(`eX : Fin M.m ≃ X`, `eY : Fin M.n ≃ Y`, entries matching), the artifact's
bracket-family complexity is a lower bound for the typed one:
every typed bracket member trims to exact sizes and flattens (rows by
`encRow`, columns by `encCol`) to an artifact-bracket member whose extracted
submatrix is value-isomorphic to the trimmed typed subgame; `D` is invariant
under the isomorphism and monotone under trimming. Consequently every
artifact lower bound on `DSet (bracket M p x y)` — monotonicity, projections,
the ladder machinery — transfers to the paper's `comp⟨M,p,x,y⟩ = Dfamily`.
Nonemptiness side conditions keep the `sInf`s honest. -/
theorem DSet_le_Dfamily {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (M : Workspace.Types.BoolMat.BoolMat)
    (eX : Fin M.m ≃ X) (eY : Fin M.n ≃ Y)
    (he : ∀ i j, M.e i j = f (eX i) (eY j))
    {p : ℕ} {x y : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hX : 1 ≤ Fintype.card X) :
    DSet (bracket M p x y)
      ≤ Dfamily (interlaceFun f p) (bracketGE X Y p x y) :=
-- CLAIM-END lem:DSet-le-Dfamily
  by exact DSet_le_Dfamily_impl f M eX eY he hx0 hx1 hy0 hy1 hX


/-! ## Reverse (DECODE) transfer and the engine-transfer equality -/

-- The digit-roundtrip: for j < n^p, encoding the digit tuple of j recovers j.
theorem encCol_digits_roundtrip {p n : ℕ} (hn : 0 < n) :
    ∀ j : ℕ, j < n ^ p →
      encCol (fun γ : Fin p => (⟨(j / n ^ (γ : ℕ)) % n, Nat.mod_lt _ hn⟩ : Fin n)) = j := by
  induction p with
  | zero =>
    intro j hj
    simp only [pow_zero, Nat.lt_one_iff] at hj
    subst hj
    simp [encCol]
  | succ p ih =>
    intro j hj
    rw [encCol_succ]
    simp only [Fin.val_zero, pow_zero, Nat.div_one]
    have htail : (fun γ : Fin p =>
        (⟨(j / n ^ ((Fin.succ γ : Fin (p+1)) : ℕ)) % n, Nat.mod_lt _ hn⟩ : Fin n))
        = (fun γ : Fin p =>
        (⟨((j / n) / n ^ (γ : ℕ)) % n, Nat.mod_lt _ hn⟩ : Fin n)) := by
      funext γ
      apply Fin.ext
      simp only [Fin.val_succ, pow_succ]
      rw [mul_comm (n ^ (γ:ℕ)) n, ← Nat.div_div_eq_div_mul]
    rw [htail]
    have hjn : j / n < n ^ p := by
      rw [pow_succ] at hj
      exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hj)
    rw [ih (j / n) hjn]
    exact Nat.mod_add_div j n

/-- MAIN CASE (0 < M.n) of the reverse transfer. -/
theorem Dfamily_le_DSet_main {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (M : BoolMat)
    (eX : Fin M.m ≃ X) (eY : Fin M.n ≃ Y)
    (he : ∀ i j, M.e i j = f (eX i) (eY j))
    {p : ℕ} {x y : ℝ} (_hx0 : 0 < x) (_hx1 : x ≤ 1) (_hy0 : 0 < y) (_hy1 : y ≤ 1)
    (_hX : 1 ≤ Fintype.card X)
    (hmX : M.m = Fintype.card X) (hnY : M.n = Fintype.card Y) (hmpos : 0 < M.m)
    (hnpos : 0 < M.n)
    -- the artifact member attaining DSet, decomposed:
    (R C : Finset ℕ)
    (hRsub : R ⊆ Finset.range (M.m * p))
    (hRequi : Workspace.Types.Equipartition.IsEquipartitioned R M.m ((M.m : ℝ) * x) p)
    (hCsub : C ⊆ Finset.range (M.n ^ p))
    (hCcard : C.card = ⌈((M.n ^ p : ℕ) : ℝ) * y⌉₊) :
    ∃ (Rt : Finset (Fin p × X)) (Ct : Finset (Fin p → Y)),
      (Rt, Ct) ∈ bracketGE X Y p x y ∧
      D (subgame (interlaceFun f p) Rt Ct) = Dmat (extract (interlace M p) R C) := by
  classical
  -- encoders (same as forward direction)
  set rowEnc : (Fin p × X) → ℕ := fun a => encRow (a.1, eX.symm a.2) with hrowEnc
  set colEnc : (Fin p → Y) → ℕ := fun c => encCol (fun γ => eY.symm (c γ)) with hcolEnc
  -- decode functions
  set colDec : ℕ → (Fin p → Y) :=
    fun j => (fun γ : Fin p => eY ⟨(j / M.n ^ (γ : ℕ)) % M.n, Nat.mod_lt _ hnpos⟩) with hcolDec
  set Rt := Finset.univ.filter (fun a : Fin p × X => encRow (a.1, eX.symm a.2) ∈ R) with hRt
  set Ct := C.image colDec with hCt
  -- injectivity of encoders
  have hrowInj : Function.Injective rowEnc := by
    intro a b hab
    rw [hrowEnc] at hab
    have := encRow_injective hab
    have h1 : a.1 = b.1 := (Prod.ext_iff.mp this).1
    have h2 : eX.symm a.2 = eX.symm b.2 := (Prod.ext_iff.mp this).2
    exact Prod.ext h1 (eX.symm.injective h2)
  have hcolInj : Function.Injective colEnc := by
    intro c d hcd
    rw [hcolEnc] at hcd
    have := encCol_injective hnpos hcd
    funext γ
    have := congrFun this γ
    exact eY.symm.injective this
  have hrowIO : Set.InjOn rowEnc Rt := hrowInj.injOn
  have hcolIO : Set.InjOn colEnc Ct := hcolInj.injOn
  -- KEY 1: Rt.image rowEnc = R
  have hRimg : Rt.image rowEnc = R := by
    apply Finset.Subset.antisymm
    · intro r hr
      rw [Finset.mem_image] at hr
      obtain ⟨a, haRt, rfl⟩ := hr
      rw [hRt, Finset.mem_filter] at haRt
      exact haRt.2
    · intro r hr
      have hrlt : r < M.m * p := Finset.mem_range.mp (hRsub hr)
      -- decode r to a typed row
      have hqlt : r / M.m < p := by
        rw [Nat.div_lt_iff_lt_mul hmpos, mul_comm]; exact hrlt
      have himod : r % M.m < M.m := Nat.mod_lt _ hmpos
      set a : Fin p × X := (⟨r / M.m, hqlt⟩, eX ⟨r % M.m, himod⟩) with ha
      have hval : rowEnc a = r := by
        rw [hrowEnc]
        show encRow (a.1, eX.symm a.2) = r
        rw [ha]
        simp only [Equiv.symm_apply_apply]
        show encRow ((⟨r / M.m, hqlt⟩ : Fin p), (⟨r % M.m, himod⟩ : Fin M.m)) = r
        show M.m * (r / M.m) + r % M.m = r
        exact Nat.div_add_mod r M.m
      rw [Finset.mem_image]
      refine ⟨a, ?_, hval⟩
      rw [hRt, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      show encRow (a.1, eX.symm a.2) ∈ R
      have : encRow (a.1, eX.symm a.2) = rowEnc a := by rw [hrowEnc]
      rw [this, hval]; exact hr
  -- KEY 2: Ct.image colEnc = C
  have hCimg : Ct.image colEnc = C := by
    rw [hCt, Finset.image_image]
    -- colEnc ∘ colDec = id on C
    have hcomp : ∀ j ∈ C, (colEnc ∘ colDec) j = j := by
      intro j hj
      have hjlt : j < M.n ^ p := Finset.mem_range.mp (hCsub hj)
      show colEnc (colDec j) = j
      rw [hcolEnc, hcolDec]
      simp only [Equiv.symm_apply_apply]
      exact encCol_digits_roundtrip hnpos j hjlt
    rw [Finset.image_congr hcomp]
    simp only [Finset.image_id']
  -- Bounds and entry-matching (mirroring forward direction)
  have hIm : (interlace M p).m = M.m * p := rfl
  have hIn : (interlace M p).n = M.n ^ p := rfl
  have hrowbd : ∀ a : Fin p × X, rowEnc a < M.m * p := by
    intro a
    rw [hrowEnc]
    have hlt : (a.1 : ℕ) < p := a.1.isLt
    have h2 : (eX.symm a.2 : ℕ) < M.m := (eX.symm a.2).isLt
    have : encRow (a.1, eX.symm a.2) < M.m * ((a.1 : ℕ) + 1) := by
      unfold encRow
      have : M.m * ((a.1 : ℕ) + 1) = M.m * (a.1 : ℕ) + M.m := by ring
      rw [this]; simp only; omega
    calc encRow (a.1, eX.symm a.2) < M.m * ((a.1 : ℕ) + 1) := this
      _ ≤ M.m * p := Nat.mul_le_mul_left M.m hlt
  have hcolbd : ∀ c : Fin p → Y, colEnc c < M.n ^ p := by
    intro c; rw [hcolEnc]; exact (encCol_digit hnpos _).1
  set Rflat := Rt.image rowEnc with hRflat
  set Cflat := Ct.image colEnc with hCflat
  have hbnd_r : ∀ a : {a // a ∈ Rt},
      (Rflat.sort (· ≤ ·)).getD (flatEquiv Rt rowEnc hrowIO a) 0 < (interlace M p).m := by
    intro a
    rw [flatEquiv_getD Rt rowEnc hrowIO a, hIm]
    exact hrowbd a.1
  have hbnd_c : ∀ c : {c // c ∈ Ct},
      (Cflat.sort (· ≤ ·)).getD (flatEquiv Ct colEnc hcolIO c) 0 < (interlace M p).n := by
    intro c
    rw [flatEquiv_getD Ct colEnc hcolIO c, hIn]
    exact hcolbd c.1
  have hentry : ∀ (a : {a // a ∈ Rt}) (c : {c // c ∈ Ct})
      (hi : (Rflat.sort (· ≤ ·)).getD (flatEquiv Rt rowEnc hrowIO a) 0 < (interlace M p).m)
      (hj : (Cflat.sort (· ≤ ·)).getD (flatEquiv Ct colEnc hcolIO c) 0 < (interlace M p).n),
      (interlace M p).e ⟨_, hi⟩ ⟨_, hj⟩ = interlaceFun f p a.1 c.1 := by
    intro a c hi hj
    have hrE := flatEquiv_getD Rt rowEnc hrowIO a
    have hcE := flatEquiv_getD Ct colEnc hcolIO c
    have hi' : encRow (a.1.1, eX.symm a.1.2) < (interlace M p).m := by
      rw [hIm]; exact hrowbd a.1
    have hj' : encCol (fun γ => eY.symm (c.1 γ)) < (interlace M p).n := by
      rw [hIn]; exact hcolbd c.1
    have hdec := interlace_entry_enc (M := M) (p := p) hmpos hnpos
      (a.1.1, eX.symm a.1.2) (fun γ => eY.symm (c.1 γ)) hi' hj'
    have hpos_r : (Rflat.sort (· ≤ ·)).getD (flatEquiv Rt rowEnc hrowIO a) 0
        = encRow (a.1.1, eX.symm a.1.2) := hrE.trans (congrFun hrowEnc a.1)
    have hpos_c : (Cflat.sort (· ≤ ·)).getD (flatEquiv Ct colEnc hcolIO c) 0
        = encCol (fun γ => eY.symm (c.1 γ)) := hcE.trans (congrFun hcolEnc c.1)
    have hlhs : (interlace M p).e ⟨_, hi⟩ ⟨_, hj⟩
        = (interlace M p).e ⟨encRow (a.1.1, eX.symm a.1.2), hi'⟩
            ⟨encCol (fun γ => eY.symm (c.1 γ)), hj'⟩ := by
      congr 1 <;> [exact Fin.ext hpos_r; exact Fin.ext hpos_c]
    rw [hlhs, hdec]
    show M.e (eX.symm a.1.2) (eY.symm (c.1 a.1.1)) = f a.1.2 (c.1 a.1.1)
    rw [he]
    simp only [Equiv.apply_symm_apply]
  -- value-iso
  have hviso : Dmat (extract (interlace M p) Rflat Cflat)
      = D (subgame (interlaceFun f p) Rt Ct) := by
    rw [hRflat, hCflat]
    exact Dmat_extract_eq_Dsubgame (interlaceFun f p) (interlace M p) Rt Ct
      rowEnc colEnc hrowIO hcolIO hentry hbnd_r hbnd_c
  -- value-iso, transported to R, C
  have hvaliso : D (subgame (interlaceFun f p) Rt Ct)
      = Dmat (extract (interlace M p) R C) := by
    rw [hviso.symm, hRimg, hCimg]
  -- colDec is injective on C (roundtrip), so Ct.card = C.card
  have hcolDecIO : Set.InjOn colDec C := by
    intro i hi j hj hij
    have hilt : i < M.n ^ p := Finset.mem_range.mp (hCsub hi)
    have hjlt : j < M.n ^ p := Finset.mem_range.mp (hCsub hj)
    have hi2 : colEnc (colDec i) = i := by
      rw [hcolEnc, hcolDec]; simp only [Equiv.symm_apply_apply]
      exact encCol_digits_roundtrip hnpos i hilt
    have hj2 : colEnc (colDec j) = j := by
      rw [hcolEnc, hcolDec]; simp only [Equiv.symm_apply_apply]
      exact encCol_digits_roundtrip hnpos j hjlt
    rw [← hi2, ← hj2, hij]
  -- bracketGE membership
  have hmemGE : (Rt, Ct) ∈ bracketGE X Y p x y := by
    refine ⟨?_, ?_⟩
    · -- ROW equipartition (GE)
      intro q _hq
      -- fiber of Rt over q bijects with R.filter (block (q:ℕ))
      have hbij :
          (Rt.filter (fun a : Fin p × X => a.1 = q)).card
          = (R.filter (fun i => M.m * (q : ℕ) ≤ i ∧ i < M.m * ((q : ℕ) + 1))).card := by
        apply Finset.card_bij (fun a _ => rowEnc a)
        · intro a ha
          rw [Finset.mem_filter] at ha ⊢
          obtain ⟨haRt, haq⟩ := ha
          rw [hRt, Finset.mem_filter] at haRt
          refine ⟨haRt.2, ?_⟩
          show M.m * (q : ℕ) ≤ rowEnc a ∧ rowEnc a < M.m * ((q : ℕ) + 1)
          rw [hrowEnc]
          exact (encRow_block_iff (m := M.m) (a.1, eX.symm a.2) (q : ℕ)).mpr (by rw [haq])
        · intro a _ b _ hab
          exact hrowInj hab
        · intro r hr
          rw [Finset.mem_filter] at hr
          obtain ⟨hrR, hblock⟩ := hr
          have hrlt : r < M.m * p := Finset.mem_range.mp (hRsub hrR)
          have hqlt : r / M.m < p := by
            rw [Nat.div_lt_iff_lt_mul hmpos, mul_comm]; exact hrlt
          have himod : r % M.m < M.m := Nat.mod_lt _ hmpos
          have hencval : encRow ((⟨r / M.m, hqlt⟩ : Fin p), (⟨r % M.m, himod⟩ : Fin M.m)) = r := by
            show M.m * (r / M.m) + r % M.m = r
            exact Nat.div_add_mod r M.m
          refine ⟨(⟨r / M.m, hqlt⟩, eX ⟨r % M.m, himod⟩), ?_, ?_⟩
          · rw [Finset.mem_filter]
            constructor
            · rw [hRt, Finset.mem_filter]
              refine ⟨Finset.mem_univ _, ?_⟩
              show encRow ((⟨r / M.m, hqlt⟩ : Fin p),
                eX.symm (eX ⟨r % M.m, himod⟩)) ∈ R
              rw [Equiv.symm_apply_apply, hencval]; exact hrR
            · -- a.1 = q
              apply Fin.ext
              show r / M.m = (q : ℕ)
              have hlo : M.m * (q : ℕ) ≤ r := hblock.1
              have hhi : r < M.m * ((q : ℕ) + 1) := hblock.2
              have h1 : (q : ℕ) ≤ r / M.m :=
                (Nat.le_div_iff_mul_le hmpos).mpr (by rw [mul_comm]; exact hlo)
              have h2 : r / M.m < (q : ℕ) + 1 := by
                rw [Nat.div_lt_iff_lt_mul hmpos, mul_comm]; exact hhi
              omega
          · -- rowEnc of decoded = r
            show rowEnc ((⟨r / M.m, hqlt⟩ : Fin p), eX ⟨r % M.m, himod⟩) = r
            rw [hrowEnc]
            show encRow (((⟨r / M.m, hqlt⟩ : Fin p)), eX.symm (eX ⟨r % M.m, himod⟩)) = r
            rw [Equiv.symm_apply_apply, hencval]
      -- so fiber card = ⌈(M.m:ℝ)*x⌉₊ = ⌈(card X:ℝ)*x⌉₊
      rw [hbij, hRequi (q : ℕ) q.isLt]
      rw [hmX]
    · -- COLUMN card (GE)
      have hCtcard : Ct.card = C.card := by
        rw [hCt, Finset.card_image_of_injOn hcolDecIO]
      rw [hCtcard, hCcard]
      -- ⌈(card Y:ℝ)^p*y⌉₊ ≤ ⌈(M.n^p:ℕ:ℝ)*y⌉₊, and they are equal
      have : ((M.n ^ p : ℕ) : ℝ) * y = (Fintype.card Y : ℝ) ^ p * y := by
        rw [hnY]; push_cast; ring
      rw [this]
  exact ⟨Rt, Ct, hmemGE, hvaliso⟩

/-- `D` of a game vanishes when either party's input type is empty. -/
theorem D_zero_of_empty {A B : Type*} [Fintype A] [Fintype B] (g : A → B → Bool)
    (h : IsEmpty A ∨ IsEmpty B) : D g = 0 := by
  have hmem : (0 : ℕ) ∈ AchievableCosts g := by
    refine ⟨Workspace.Types.Protocol.Protocol.leaf false, rfl, ?_⟩
    intro a b
    rcases h with hA | hB
    · exact (hA.false a).elim
    · exact (hB.false b).elim
  exact Nat.le_zero.mp (Nat.sInf_le hmem)

/-- Degenerate reverse case: when `p = 0` (empty rows) or `Fintype.card Y = 0`
with `p ≥ 1` (empty columns), the typed family complexity is `0`, hence `≤`
anything. -/
theorem Dfamily_zero_degenerate {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) {p : ℕ} {x y : ℝ} (hx1 : x ≤ 1) (hy1 : y ≤ 1)
    (hX : 1 ≤ Fintype.card X)
    (hdeg : p = 0 ∨ (0 < p ∧ Fintype.card Y = 0)) :
    Dfamily (interlaceFun f p) (bracketGE X Y p x y) = 0 := by
  classical
  -- a member exists
  obtain ⟨RC, hRC⟩ := bracketGE.nonempty (X := X) (Y := Y) p x y hx1 hy1 hX
  -- its subgame has an empty party
  have hempty : IsEmpty {a // a ∈ RC.1} ∨ IsEmpty {c // c ∈ RC.2} := by
    rcases hdeg with hp0 | ⟨_, hY0⟩
    · left
      subst hp0
      have : IsEmpty (Fin 0 × X) := by
        constructor; rintro ⟨q, _⟩; exact q.elim0
      exact Subtype.isEmpty_of_false (fun a => (this.false a).elim)
    · right
      have hYempty : IsEmpty Y := Fintype.card_eq_zero_iff.mp hY0
      have : IsEmpty (Fin p → Y) := by
        constructor; intro g
        have hpne : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
        exact hYempty.false (g hpne.some)
      exact Subtype.isEmpty_of_false (fun c => (this.false c).elim)
  have hDzero : D (subgame (interlaceFun f p) RC.1 RC.2) = 0 :=
    D_zero_of_empty _ hempty
  apply Nat.le_zero.mp
  apply Nat.sInf_le
  exact ⟨RC, hRC, hDzero.symm⟩

/-- Full reverse transfer (DECODE direction). -/
theorem Dfamily_le_DSet_impl {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (M : BoolMat)
    (eX : Fin M.m ≃ X) (eY : Fin M.n ≃ Y)
    (he : ∀ i j, M.e i j = f (eX i) (eY j))
    {p : ℕ} {x y : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hX : 1 ≤ Fintype.card X) :
    Dfamily (interlaceFun f p) (bracketGE X Y p x y)
      ≤ DSet (bracket M p x y) := by
  classical
  have hmX : M.m = Fintype.card X := by
    have := Fintype.card_congr eX; rwa [Fintype.card_fin] at this
  have hnY : M.n = Fintype.card Y := by
    have := Fintype.card_congr eY; rwa [Fintype.card_fin] at this
  have hmpos : 0 < M.m := by rw [hmX]; exact hX
  -- degenerate branches: p = 0 or M.n = 0
  rcases Nat.eq_zero_or_pos p with hp0 | hppos
  · rw [Dfamily_zero_degenerate f hx1 hy1 hX (Or.inl hp0)]
    exact Nat.zero_le _
  rcases Nat.eq_zero_or_pos M.n with hn0 | hnpos
  · have hY0 : Fintype.card Y = 0 := by rw [← hnY]; exact hn0
    rw [Dfamily_zero_degenerate f hx1 hy1 hX (Or.inr ⟨hppos, hY0⟩)]
    exact Nat.zero_le _
  -- MAIN CASE: 0 < p, 0 < M.n.
  -- Artifact bracket nonempty (via bracketGE.nonempty + bridge_bracket).
  obtain ⟨RC0, hRC0⟩ := bracketGE.nonempty (X := X) (Y := Y) p x y hx1 hy1 hX
  obtain ⟨R0, C0, hR0sub, hR0equi, hC0sub, hC0card, hmemMat0⟩ :=
    bridge_bracket (X := X) (Y := Y) (p := p) (x := x) (y := y) RC0 hRC0
  have hbrne : (bracket M p x y).Nonempty :=
    ⟨_, hmemMat0 M hmX hnY⟩
  -- DSet is attained: pick a member g realizing it.
  have hsetne : { c : ℕ | ∃ g ∈ bracket M p x y, Dmat g = c }.Nonempty := by
    obtain ⟨g, hg⟩ := hbrne
    exact ⟨_, g, hg, rfl⟩
  have hmem := Nat.sInf_mem hsetne
  obtain ⟨g, hgmem, hgeq⟩ := hmem
  have hDSeteq : DSet (bracket M p x y) = Dmat g := by
    rw [DSet]; exact hgeq.symm
  -- decompose g
  obtain ⟨R, C, hRsub, hRequi, hCsub, hCcard, hgext⟩ := hgmem
  subst hgext
  -- apply main-case helper
  obtain ⟨Rt, Ct, hmemGE, hviso⟩ :=
    Dfamily_le_DSet_main f M eX eY he hx0 hx1 hy0 hy1 hX hmX hnY hmpos hnpos
      R C hRsub hRequi hCsub hCcard
  rw [hDSeteq, ← hviso]
  -- Dfamily ≤ D (subgame f Rt Ct)
  apply Nat.sInf_le
  exact ⟨(Rt, Ct), hmemGE, rfl⟩


-- CLAIM-BEGIN lem:Dfamily-le-DSet
/-- THE VALUE-LEVEL TRANSFER, REVERSE (DECODE) DIRECTION. Same presentation
data as `DSet_le_Dfamily` (a typed game `f`, a `BoolMat` `M` presenting the
same matrix through `eX : Fin M.m ≃ X`, `eY : Fin M.n ≃ Y`, entries matching):
the typed bracket-family complexity is a lower bound for the artifact one.
The artifact bracket is nonempty (a typed member from `bracketGE.nonempty`
flattens via `bridge_bracket` to a matching-dimension member), so `Nat.sInf_mem`
exhibits an artifact member `g = extract ⟨M⟩^p R C` attaining `DSet`. Decoding
`R` by `encRow` and `C` digit-by-digit (`encCol_digits_roundtrip`) to a typed
member `(Rt, Ct) ∈ bracketGE X Y p x y` makes `R = Rt.image encRow`,
`C = Ct.image encCol`, so `Dmat_extract_eq_Dsubgame` gives
`Dmat g = D (subgame (interlaceFun f p) Rt Ct)`; the `sInf` defining `Dfamily`
is then `≤` that value. Degenerate `p = 0` (empty rows) and `card Y = 0` with
`p ≥ 1` (empty columns) force `Dfamily = 0` and are discharged separately. With
`DSet_le_Dfamily` this closes the two-way transfer (see `Dfamily_eq_DSet`),
placing the artifact's entire bracket engine behind the paper's typed
`comp⟨M,p,x,y⟩ = Dfamily`. -/
theorem Dfamily_le_DSet {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (M : Workspace.Types.BoolMat.BoolMat)
    (eX : Fin M.m ≃ X) (eY : Fin M.n ≃ Y)
    (he : ∀ i j, M.e i j = f (eX i) (eY j))
    {p : ℕ} {x y : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hX : 1 ≤ Fintype.card X) :
    Dfamily (interlaceFun f p) (bracketGE X Y p x y)
      ≤ DSet (bracket M p x y) :=
-- CLAIM-END lem:Dfamily-le-DSet
  by exact Dfamily_le_DSet_impl f M eX eY he hx0 hx1 hy0 hy1 hX

-- CLAIM-BEGIN lem:engine-transfer
/-- THE ENGINE-TRANSFER EQUALITY. Under the union of both directions'
hypotheses, the paper's typed family complexity `comp⟨M,p,x,y⟩ = Dfamily`
equals the artifact's set complexity `DSet (bracket M p x y)`. Proof:
`le_antisymm` of `Dfamily_le_DSet` and `DSet_le_Dfamily`. Every artifact lower
bound on `DSet` now transfers verbatim to `Dfamily`, and vice versa. -/
theorem Dfamily_eq_DSet {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (M : Workspace.Types.BoolMat.BoolMat)
    (eX : Fin M.m ≃ X) (eY : Fin M.n ≃ Y)
    (he : ∀ i j, M.e i j = f (eX i) (eY j))
    {p : ℕ} {x y : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hX : 1 ≤ Fintype.card X) :
    Dfamily (interlaceFun f p) (bracketGE X Y p x y)
      = DSet (bracket M p x y) :=
-- CLAIM-END lem:engine-transfer
  le_antisymm
    (Dfamily_le_DSet f M eX eY he hx0 hx1 hy0 hy1 hX)
    (DSet_le_Dfamily f M eX eY he hx0 hx1 hy0 hy1 hX)

end NPCC
