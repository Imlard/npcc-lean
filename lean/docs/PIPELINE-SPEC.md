# PIPELINE-SPEC v1 — the minimal formalization loop (decision (b), 2026-07-06)

> **Historical pipeline specification.** This records the production process,
> not the current mathematical trust boundary. See `../AUDIT.md` and
> `../BUILD.md` for release verification.

**Objective.** One pipeline, one target: drive the Target-A then Target-B obligations of the
NP-hardness formalization to sorry-free, axiom-audited, faithfulness-signed Lean, using the
Beyond-the-Library blueprint. The pipeline exists to be *tuned in place*, not extended.
**The compiler is the only truth. Sorry-count on a fixed obligation DAG is the only
progress metric.** No KB writes, no solve-loop coupling, no new arms.

## The five components (all v1-minimal, interfaces are files)

**C1 — Obligation ledger** (`C:\lean\npc-cc\obligations.json`, mirrored). The fixed DAG.
One record per obligation: `id` (paper label, e.g. `lem:coord-projection`), `kind`
(def | bridge | aux-lemma | lemma | port-check), `statement_tex` (verbatim from the frozen
arXiv v4 source — never paraphrased), `deps` (ids), `lean_name`, `file`, `status` ∈
{open → stated → sorry-closed → proved | axiom | parked}, `attempts` (count + digests),
`signed_off` (bool, Simon). Only the loop mutates it; humans audit. The DAG is FROZEN per
target — adding obligations mid-target requires a logged decomposition event (C4), never
silent scope growth.

**C2 — Prover-worker.** One obligation in, one Lean patch out. Input pack: the obligation's
`statement_tex` + frozen-tex excerpt around it, the available Lean context (relevant
`Workspace.*`/`NPCC.*` decl signatures, NOT whole files), prior-attempt digests. Contract:
the worker may write proof body + `private` helpers only. Lanes: Claude subagent (primary),
codex GPT-5.5 xhigh via model-bridge (second lane for stuck items). Statements are NEVER
authored by the prover lane — they come from C5.

**C3 — Compiler verdict.** `lake env lean <file>` (the ~40 s full-import cost is accepted
in v1; a REPL server is explicitly deferred). Structured parse of errors. Two gates on any
status flip toward closed: (a) **Claim Check** — the obligation's statement text in the file
is byte-identical to the registered one (checker script, not model judgment); (b)
**axiom gate** — `#print axioms` output ⊆ {propext, Classical.choice, Quot.sound} ∪ declared
policy axioms (01-boundary-certificate). Only C3 may mark sorry-closed/proved. Every
milestone additionally does a clean `lake build` + full-DAG axiom report, mirrored.

**C4 — Structured-failure router.** Maps (verdict, worker self-report) → one of:
`retry` (max 3 attempts per lane, then forced route change) · `reformulate` (statement
suspected wrong → back to C5 + Simon) · `decompose` (promote to non-leaf; children enter
the ledger via a logged event; **parent-before-children**: parent must first close from
children's statements as sorry-premises) · `escalate-human` (faithfulness/mathematical
question for Simon) · `park` (blocked; parked items are visible, never silently dropped).
Budgets are hard-coded and small; the router never invents new obligation kinds.

**C5 — Faithfulness judge** (statements only; proofs are C3's job). For every `def`/lemma
statement: Hint-Cleaner strips comments → two lanes: blind back-translation (model A
informalizes the Lean, model B compares to `statement_tex`) + direct comparison (different
model family) → adjudicator merges → **Simon signs off** before status becomes `stated`.
Every new definition ships 3–5 general auxiliary unit-test lemmas that must close before
any dependent fires (BtL aux-lemma discipline).

## Doctrine bindings
Type-first; parent-before-children; Claim Check byte-identity; Hint Cleaner before judging;
axiom policy per `deployment-pack/01-boundary-certificate.md` (AGHP, source NP-hardness,
large-d bundle — nothing else, ever, without editing that file first); frozen text =
`paper-snapshots/arxiv-2508.05597-src/main.tex` only.

## Ultra lane — GPT-5.5 Pro via browser (BINDING, Simon 2026-07-06)
For CRITICAL work, the two fast judge lanes (codex xhigh + Opus) are necessary but not
sufficient: **every keystone-class item also gets a GPT-5.5 Pro (browser Ultra)
faithfulness packet**, fired asynchronously (fire-and-harvest via the ultra-fire
workflow; per-project pending store `npc-cc`) and harvested at the next checkpoint.
- Keystone-class = new definitions; engine lemmas (ladder/partition/separation family);
  any statement whose misreading would poison a subtree (bridges, transfer theorems);
  and design decisions of encoding rank (e.g. typed-vs-flattened class choices).
- Packets are SELF-CONTAINED (frozen tex excerpt + exact Lean + declared conventions +
  targeted questions); an Ultra "confirmed" NEVER substitutes for the compiler, and an
  Ultra objection routes to reformulate exactly like a Simon objection.
- Harvests are recorded in pipeline/judgments/ and MUST be folded in before the
  corresponding ratification is considered settled.

## Shakedown plan
**M-A (Target A):** ~12 obligations — `NPCC.IsEquipartitionedGE` + `NPCC.bracketGE` (+ their
aux unit tests), bridges to the artifact's exact-card forms, `coord-projection`, seed-rank
port-check. Done = all sorry-free, axiom-clean, signed. **M-B (Target B):** Stage-1
threshold package (`claim:stage1-rect-bound` → `cor:stage1-chosen-dense-threshold`) — the
first genuinely new proofs (heavy-path + balancedness counting). Only after M-B do we
*discuss* scaling (A′ engine, C, D). v1 explicitly does NOT build: REPL/MCP server,
best-of-k auctioneer (single candidate until close-rate demands otherwise), dashboards,
parallel fan-out >2, KB integration.

## Kill criteria (armed before the first line of code)
- **K1 — close-rate:** ≥50 attempts across ≥10 obligations with sorry-close rate <20% and
  falling → STOP; reassess granularity/worker mix with Simon. No silent grinding.
- **K2 — infrastructure recursion:** any component needing a second rewrite before M-A →
  STOP. We are proving, not building; a loop that needs rebuilding pre-M-A is the repo's
  documented failure mode recurring.
- **K3 — UMD engagement:** a collaborative reply from the BtL team → freeze v1 where it
  stands, converge on their pipeline; v1 artifacts (ledger, judge, gates) remain useful.
- **K4 — wall-clock:** M-A not reached within 7 running days → STOP and review with Simon.
- **K5 — faithfulness dispute:** any statement dispute unresolved >2 days → park that
  subtree. We never "interpret around" the paper.

## Weekly honest readout (replaces dashboards)
One short note per running day in `formalization/loop-log.md`: obligations closed / open /
parked, attempts spent, axioms in force, disputes pending, kill-criteria distances. Written
by the loop, read by Simon. If the note flatters, the note is wrong.
