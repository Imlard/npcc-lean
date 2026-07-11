# Lean formalization of "NP-Completeness of Deterministic Communication Complexity via Relaxed Interlacing"

> **Historical planning document.** It records the original workflow and may
> contain obsolete paths, targets, or scope language. Use `../AUDIT.md` and
> `README.md` for the current release.

> **STRATEGY UPDATE 2026-07-06 (user-endorsed, per GPT-5.5 Pro review): CONTACT-FIRST.**
> Email the Beyond-the-Library team proposing this paper as their next benchmark /
> collaboration (draft + deployment pack in `deployment-pack/`); run only a capped one-week
> local pilot in parallel (Target A of `deployment-pack/03-theorem-map-and-targets.md`);
> full pipeline recreation below is the FALLBACK if they decline or go silent.
> Extra ask in the email: their lakefile/toolchain pin (not published on FormaliaXiv).
> Credit framing: collaboration / companion formalization paper, not a tool request.

**Mission** (Simon, 2026-07-06): produce a machine-checked Lean 4 formalization of the
Gaspers–He–Mackenzie NP-completeness paper — the follow-up to the direct-sum refutation —
following the "Beyond the Library" recipe (arXiv:2606.31134, ingested at
`Tooling/research/autoformalization-agentic-lean-2026-07-06/`). That pipeline already
formalized the ANCESTOR paper (Mackenzie–Saffidine STOC'25) axiom-free; its published Lean
artifact is mirrored here and is our foundation.

## Assets in place

- **Paper sources**: `manuscript/main.tex` (live rewrite surface per repo README), root
  `main.tex` (arXiv build), `paper-snapshots/Arxiv_NP_Hardness_of_CC-2026-07-06.pdf` (87pp,
  the version Simon supplied as the formalization target). `docs/LIVE_MAP.md`,
  `docs/PROOF_SPINE.md`, `docs/KNOWN_FACTS.md`, `docs/CERTIFICATION_LOG.md` give the
  agent-ready map of the proof.
- **Reference Lean artifact**: `formalization/reference-lean/Refuting/` — the complete
  Beyond-the-Library formalization of Mackenzie–Saffidine (34 files, 295 decls, **0 sorries,
  0 axioms**; inventory in `formalization/REUSE-INVENTORY.md`). Fetched from
  beyondthelibrary.github.io/formal_arxiv (their lakefile/toolchain are not published; the
  files `import Mathlib` wholesale, so we re-host them in our own workspace and re-verify).
- **Toolchain**: elan 4.2.3 / Lake 5.0.0 / Lean 4.30.0 already installed at `C:\Users\User\.elan`.

## The reuse goldmine (what we do NOT have to build)

The new paper imports from mackenzie2025refuting exactly: monotonicity, maximum projection,
product of projections, transpose symmetry, and the rank bound for the seed [1 0]
(new paper's Lemma `rankclaim` = M&S Lemma 2.5). **All of these are already formalized**:

| New paper item | Refuting artifact decl (file) |
|---|---|
| Boolean matrix / game | `BoolMat` (Types/BoolMat) |
| Protocol tree, cost = depth | `Protocol`, `Protocol.cost` (Types/Protocol) — exactly the depth model |
| D(f) deterministic CC | `D` via `sInf AchievableCosts` (Types/CommComplexity); `Dmat`, `DSet` (Types/MatComplexity) |
| p-fold interlace (Def 2.1) | `interlaceFun`, `interlace` (Types/Interlace) |
| restricted submatrix ε(G,R,C) | `extract` (Types/Extract) |
| (Q,T)-equipartition (Def 2.3) | `IsEquipartitioned` (Types/Equipartition) — NOTE: exact-cardinality variant; the new paper uses ≥ T. Alignment shim needed. |
| bracket family ⟨M,p,x,y⟩ (Def 2.4) | `bracket` (Types/Bracket) |
| Λ_M(p,x,y) three-rung | `Lambda` (Types/Lambda) — verbatim the same min over j∈{0,1,2} |
| Lemma mono / max-projection / product-of-projections / one-copy transpose | `monotonicity`, `extended_maximum_projection`, `extended_product_of_projection`, `transpose_bracket`, `Dmat_extract_transpose` (BracketLemmas) |
| one-step partition & ladder steps (App. A) | `lemma_A1_partition_recurrence`, `lemma_A3_row_ladder_step` (= lem:lambda-row-step), `lemma_A4_column_ladder_step` (= lem:lambda-col-step, with the y^{1/(1+τ)}, y^{τ/(1+τ)} split) (Appendix.lean) |
| balancing-by-blocks (lem:block-balancing) | `extended_balancing` (BracketLemmas) — close variant, check exact statement |
| rank bound for seed (lem:rankclaim) | LogRankBound.lean (verify it covers interlace of [1 0]) |
| subgames are easier (Prop 3.11 of M&S) | `subgames_are_easier` |

**Step 0 of any prover run: re-verify this layer compiles under our pinned Mathlib, then
treat matched decls as the definitional substrate. Every reused definition must pass the
faithfulness check against the NEW paper's definitions (they drifted: ≥T vs =T equipartition,
column multisets for relaxed interlace, etc.).**

## What is genuinely new to formalize

Layered exactly as the paper's proof spine (Fig. 1), each layer consumed as a black box by
the next — formalize in this order, **proving each parent from its children's statements
(sorry premises) before descending** (Beyond-the-Library parent-first discipline):

1. **Classical lower-bound engine (§2)** — two-copy ladder (lem:two-copy-ladder), robustness
   definition (R1–R4), odd-copy seed (lem:odd-copy-seed-rungs), **iterated
   density-amplification (lem:new-partition)** with the (t,r) grid induction, exponents
   E_{t,r}, bridge inequalities; power-of-two LB (cor:power-of-two). Ingredient ladder steps
   already exist (A1/A3/A4). Pure finite combinatorics + elementary real arithmetic. RISK: low.
2. **Classical protocol control (§3)** — no-waste row-only partition, failure-to-separate,
   **classical near-exact separation (lem:classical-separation-clean)** by induction on the
   first log q bits. RISK: low-medium (protocol-tree surgery: "restrict protocol to a subgame"
   infrastructure exists in the artifact's UpperBound/Projections files).
3. **Relaxed interlace (§4)** — (q,t)-balanced column families (Def), relaxed interlace over
   an indexed family (multiset columns!), projection closure, balancing-by-blocks,
   **bridge lemma (lem:relaxed-to-classical)**, column-loss resilience, **extension theorem
   (thm:Extension)** and **relaxed near-exact separation (thm:SeparationTheorem)** (3-phase
   proof). RISK: medium — new types; the AGHP existence (rem:balanced-columns-exist) is the
   one *cited* external ingredient → admit as a clearly-labeled axiom in round 1
   ("AGHP small-bias sample spaces exist and are polytime-constructible"), de-axiomatize in
   phase 2 only if desired (formalizing AGHP itself is a known formalization project size).
4. **Reduction (§5 + App. C)** — {0,1}-VBP hardness from 4-Colouring (formalize; 4-Colouring
   NP-hardness = citation axiom or import), zero-anchor preprocessing, the audited parameter
   scaffold (q1, I1, r1, b0/b1, q2, I2, r2, h2, h'2...), stages M0→M1→M2→M3→M4, Stage-1
   threshold (heavy-path counting), Stage-2 certification lemmas, Stage-3 bin separation,
   Stage-4 gadget lemmas, fibre survival, MFourNoWasteLift synchronisation, final one-bit gap.
   RISK: highest — parameter-heavy, "for all sufficiently large d" everywhere. Policy:
   formalize with explicit `∃ d★, ∀ d ≥ d★ (power of two), ...` and discharge the ~15
   large-d inequalities (the paper's App. C checklist table enumerates them — use it as the
   obligation list). The audited-parameter table (tab:reduction-parameters) becomes a Lean
   `structure ScaffoldParams` with the concrete definitions.
5. **Headline statement.** Two-layer strategy:
   - **Layer A (the mathematical theorem, unconditional):** a polytime-size, explicitly
     computable map I ↦ (M4, k) with: YES ⇒ D(M4) ≤ k (lem:scaffold-completeness) and
     NO ⇒ D(M4) > k (the NO-case theorem), plus |M4| = poly(|I|) as explicit bounds
     (lem:polytime as a size statement). This is the paper's entire mathematical content
     and is what human experts should check faithfulness of.
   - **Layer B (the NP-completeness wrapper):** express "polytime reduction" formally.
     Options, in order of preference: (i) Mathlib computability (`Turing.TM2ComputableInPolyTime`)
     if workable; (ii) a scoped complexity-theory mini-framework with the source problem's
     NP-hardness as a citation axiom (mirrors the paper, which cites 4-Colouring hardness);
     (iii) Layer B stated in the README as the routine glue, à la Beyond-the-Library's
     "algorithmic results not formalized" limitation. Decide after a 1-day spike on (i).

## Pipeline (Beyond-the-Library recipe + our arms)

- **Orchestrator** = Claude Code session in this repo. Statement pipeline first (Extractor →
  Type Planner → per-type k-candidate formalizers with **auxiliary-lemma unit tests** →
  Auctioneer → Faithfulness Judge with Hint-Cleaner and cross-model blind back-translation),
  then proving pipeline (NL Prover ↔ Proof Critic in-agent loop → Proof Detailer → Lemma
  Breakdown → Lemma Leanifier → Prover with **Claim Check byte-identity** on every closed
  statement; parent-before-children; structured failure routing; prior work only via
  citation-tagged axioms).
- **Cross-model judging**: GPT-5.5 xhigh via model-bridge = rigor authority for informal-proof
  critique and faithfulness verdicts (our validated judge); Gemini for the second blind lane.
  Ultra tier (Pro Extended / Deep Think) reserved for frozen cruxes (stuck lemmas).
- **Tools needed**: Lean REPL loop (lake env + a REPL script or `lean-lsp-mcp`), LeanSearch /
  Loogle for Mathlib lookup, `#print axioms` gate in CI to enforce the axiom policy.
- **Faithfulness protocol**: every formalized definition ships 3–5 general auxiliary lemmas
  proved before use; every theorem statement gets blind back-translation + direct comparison
  by two model families; the paper's own `docs/KNOWN_FACTS.md` + certification log are the
  reference for intent.

## Workspace decision (pending)

Lake project should NOT live on Google Drive (mathlib cache ≈ 5–7 GB, tens of thousands of
files, Drive sync churn). Proposal: `C:\lean\npc-cc\` real disk via sandbox-off writes
(user-visible), git-init with remote = this repo's `formalization/lean-mirror/` (source files
only, .lake ignored) so sources stay in Drive/git while builds stay local. Toolchain: pin
latest stable Lean + Mathlib; port the Refuting artifact into the workspace as `Refuting/`
library and fix any Mathlib-drift breakage first (that build doubles as the reuse
verification).

## Scale estimate (honest)

Beyond-the-Library data points: M&S ≈ 12k lines, 9.2M output tokens, ≈$1.7k API-equivalent,
weeks of wall-clock on one $200 subscription; Kalai et al. ≈ 30k+ lines, 16M output tokens.
This paper is larger and more parameter-dense than any of their five (87pp; four-stage
scaffold). Working estimate: **30–60k Lean lines, 1–3 subscription-months of steady
background running**, front-loaded by the ~40% head start from the Refuting artifact on
layers 0–1. Deliverable-grade milestones: (M1) engine layer sorry-free; (M2) separation
theorems sorry-free; (M3) Stage-1 threshold + scaffold definitions; (M4) NO-case theorem
sorry-free modulo declared axioms; (M5) axiom audit + de-axiomatization pass.

## Risks / honest flags

- **Version skew — RESOLVED 2026-07-06**: canonical = the arXiv version (FOCS rejected).
  See `paper-snapshots/VERSION-FREEZE.md`: PDF snapshot present; the arXiv .tex is newer
  than every tex in this repo (discriminator sentences logged) and Simon is dropping it
  into `paper-snapshots/main-arxiv-canonical.tex`. Claim-Check binds to that file, never
  the live rewrite.
- **Equipartition/bracket definitional drift** between the artifact (=T, exact card) and the
  new paper (≥T): resolve at Type-Planner stage with an explicit bridging lemma, not by
  silently editing either.
- **Concurrent work**: Hirahara–Ilango–Loff also prove NP-hardness; the formalization's
  scientific value is the **relaxed-interlacing framework as reusable machine-checked
  tools** (extension + separation theorems as Lean lemmas others can apply), not just the
  headline bit. Prioritize framework layers accordingly.
- Formalizing may surface paper gaps (BtL found one in Pham) — treat any such finding as a
  win for the FOCS/next-venue version; route through `docs/` logs.
