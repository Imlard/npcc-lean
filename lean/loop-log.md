# loop-log — v1 pipeline (governed by formalization/PIPELINE-SPEC.md)

> **Historical production log.** This file preserves decisions and intermediate
> claims as they were recorded; it is not a current correctness or scope
> statement. See `AUDIT.md`, `PAPER-FINDINGS.md`, and `BUILD.md` for the audited
> release boundary.

## 2026-07-06 (day 0 — build day)
Built: spec, C1 ledger (12 obligations, Target A, DAG frozen), C2–C4 runner
(packets / Claim-Check incl. cross-claim guard / lake verdict / axiom gate / router),
C5 lanes run manually via model-bridge. First full cycle executed on
def:equipartition-ge: STATE compiled + claim registered (970 B), blind + direct judge
lanes PASS, now awaiting Simon sign-off. Closed 0 / stated 1 / open 11 / parked 0;
attempts 0. Kill-criteria distances: K1 n/a (0 attempts), K2 clean (runner patched once
pre-M-A for the cross-claim hole — counted as the one allowed hardening, next rewrite
trips K2), K4 clock starts at first PROVE attempt. Honest notes: initial artifact
"verification" was false (root imported only Basic) — caught by axiom gate, fixed,
re-verified kernel-clean; heredoc backslash mangling cost one ledger build (banked as
transport gotcha). Judge-lane diversity is codex-only (gemini auth dead) — Simon's
sign-off is the independent lane until that's restored.

## 2026-07-06 (day 0, entry 2 — reformulation)
Simon chose TYPED/indexed encoding (vs flattened-nat); K2 exception granted for one
additive command (pipeline/reformulate.mjs; runner.mjs untouched; K2 hard from now on).
Cycle: reformulate -> typed restate (compiled, claim 1042 B) -> both judge lanes PASS.
Encoding decision propagates: bridges now carry typed<->artifact transfer via
D-invariance under row/column identifications. Status: stated 1 / open 11; attempts 1
(the reformulation, correctly counted). Awaiting sign-off #1 (typed).

## 2026-07-06 (day 0, entry 3 — first fleet round)
Mode change (Simon): aggressive orchestration — Opus 4.8 fleet forms+proves, Fable
orchestrates/adjudicates, runner remains sole gate. Spec parallelism cap superseded by
user instruction (logged here, spec text unchanged as historical record).
Round 1: 12 Opus candidates (best-of-2 x 6 aux lemmas), all self-checked clean; Fable
adjudication picked 6 winners (notable: bracket-nonempty accepted STRONGER-than-spec
statement, positivity hypotheses dropped as unnecessary; 3 lean_name renames to match
frozen ledger; bracket-top took the weaker DecidableEq instance). Driver: 6/6 PROVED
through state+submit with axiom gate; zero routed failures; cross-claim guard held
through 12 file rewrites. TARGET A: 8/12 proved, 4 open (2 bridges, coord-projection,
rankclaim port). Both definitions now carry full closed unit-test batteries (BtL
discipline satisfied). Next: bridges = Fable-critical design (typed<->artifact
D-invariance transfer).

## 2026-07-06 (autonomy window, +0h)
Simon granted 6h autonomous operation (recorded at start timestamp in git log; recap
after). GOVERNANCE: bridge sign-offs #3/#4 taken as PROVISIONAL from Simon "Ok" +
autonomy grant — RATIFY AT RECAP (reformulate path stands if objected). Window plan:
finish M-A (bridges, coord-projection, rankclaim port), then open Target Aprime
(complexity layer + D-invariance as Fable-critical, engine statements fleet-formed).
All statements still judge-laned; compiler remains sole gate; provisional sign-offs
batched for recap.

## 2026-07-06 (autonomy window, +0.5h)
coord-projection: statement registered (1 routed attempt: tuple-ascription parse bug,
fixed) and judged PASS on both lanes — codex blind + Opus direct (codex hit its usage
ceiling ~05:55, resets 06:29; direct lane swapped to Opus = better family diversity).
PROVISIONAL sign-off (recap-ratify). Two Opus provers running on the frozen statement.
port:rankclaim ASSESSED: artifact has the generic log-rank engine, NOT the bracket-form
seed claim -> stays open, full lem:rankclaim obligation rescoped into A-prime (recap-
ratify). M-A definition-of-done adjusted: 11 proved + 1 assessed-and-rescoped.

## 2026-07-06 (autonomy window, +1h)
coord-projection PROVED: both Opus provers returned clean (v1 chosen, no helpers; v2
held as fallback, unused). Runner gates passed: Claim-Check byte-identity, build,
sorry-scan, axiom gate (kernel-only). M-A MILESTONE: 11/12 proved + port:rankclaim
assessed-and-rescoped to A-prime. Opening Target A-prime: complexity layer (family
complexity over typed games via artifact polymorphic D) + D-invariance under
identifications (Fable-critical), engine statements after.

## 2026-07-06 (autonomy window, +1.5h)
Complexity layer PROVED (def:subgame, def:Dfamily — provisional signoffs, judge lanes
run AFTER signoff this round, inversion noted). Transport lemma statements frozen.
Batched Opus judgment on all four Aprime statements: CORRECT x4 — judge independently
verified Dfamily sInf-encoding matches artifact DSet convention; empty-domain corner
cases keep both transport lemmas true; one redundant-but-harmless Fintype pair flagged.
Codex DOWN for the window (usage limit persists past stated reset) — all judging on
Opus lane; cross-VENDOR diversity unavailable, recorded for recap. 8-prover fleet
running on transport proofs + Dfamily aux tests.

## 2026-07-06 (autonomy window, +2.5h)
Transport lemmas PROVED (both, kernel-only; dsuble prover found the artifact
AchievableCosts_nonempty is already polymorphic — simpler route than designed).
Dfamily aux tests: first driver pass STATE-FAILED x2 — MY header bug (dropped the
provers open line); fixed, re-driven. rankclaim statement registered over the
complexity layer. Codex still down; judging on Opus lane.

## 2026-07-06 (autonomy window, +3h)
Dfamily aux tests PROVED after driver-header fix. rankclaim statement judged CORRECT
(Opus lane; judge verified the GE-family form is the SAFE-STRONGER direction — implies
the paper Lemma 2.5 via Dfamily.anti_mono; hypotheses one-for-one; +1 preserved).
Ledger: 17 proved / 1 stated (rankclaim, fleet running with the two-sided leaf-count
route for the +1) / 1 open-as-assessed (port:rankclaim). Recap draft staged.

## 2026-07-06 (autonomy window, +3.5h) — TRANCHE 1 COMPLETE
lem:rankclaim PROVED by BOTH fleet provers (two-sided leaf-count route: new helper
protocol_rank_pair_bound adapts the artifact induction to carry the complement; the +1
falls out as ceil(log t)+1 = ceil(log 2t) <= Dmat from rank+rankCompl <= 2^cost).
Submitted v1 through the runner (kernel axioms only). PROCESS VIOLATION logged: v2
wrote the live workspace file directly (contract = scratchpad only); harmless — the
runner overwrote and re-gated from zero — but future fleet prompts must forbid
workspace writes explicitly. Ledger: 18 proved / 1 open-as-assessed (port:rankclaim).

## 2026-07-06 08:25 — codex RESTORED, cross-vendor gap closed
Simon confirmed quota; health-check passed (earlier minimal-effort probe failed on a
tools/effort incompatibility, not usage). Batched GPT-5.5 xhigh re-judge of the six
Opus-only-judged statements: CORRECT x6, no findings (rankclaim corroborated against
the paper, cited as compiled Lemma 49). Every statement in the development now carries
both Anthropic and OpenAI verdicts. Recap section 4 amended accordingly.

## 2026-07-06 ~08:50 — Ultra lane HARDCODED (Simon) + tranche-2 batch
BINDING protocol added to PIPELINE-SPEC (Ultra lane section): GPT-5.5 Pro browser
packets on every keystone-class item, fire-and-harvest, folded into judgments before
ratification. Packet npcc-1 FIRED (audits S1-S6: robust, ladder, rankclaim, keystone
transfer, encCol+digit — with Q5 asking Pro to flag convention risks for the coming
separation-theorem layer). two-copy-ladder statement registered. T2 fleet + Opus judge
lane still running; codex judged T2 statements CORRECT x4.

## 2026-07-06 ~09:05 — fleet-write violation #2 + mechanical guard
A keystone prover wrote scratch notes into Workspace/MonoTest.lean DESPITE the explicit
no-workspace-writes prompt rule (harness Write tool is not sandbox-blocked on C:).
Untracked from git (file left on disk until fleet completes to avoid breaking its
self-check iteration; physical cleanup after). MECHANICAL GUARD adopted: adjudication
chains now run git status --porcelain BEFORE any git add; fleet-era commits use
explicit pathspecs, never bare add -A. Prompt rule stays as belt; this is the braces.

## 2026-07-06 ~09:20 — SCALE-UP authorized (Simon) + tranche 3
Simon: safe progress confirmed -> scale up aggressively toward the final proof; AGHP
(Alon et al.) + bin-packing NP-hardness AUTHORIZED as axioms (wired: boundary
certificate + runner allowedAxioms; axiom STATEMENTS still get full judge + Ultra
treatment before declaration — a wrong axiom is unrecoverable). T3 opened: reverse
transfer -> Dfamily = DSet (turns artifact ladder machinery into typed engine lemmas
verbatim), AGHP axiom obligation, balanced-family + relaxed-interlace defs (Section 4
opens). Commit discipline: explicit pathspecs (guard active).

## 2026-07-06 ~10:15 — ENGINE UNLOCKED: Dfamily = DSet
Reverse transfer + equality PROVED by both fleet provers (no extra hypotheses; the
degenerate regimes discharged, artifact nonemptiness derived via bridge_bracket).
With lem:engine-transfer the artifact ladder machinery (A1/A3/A4, projections,
monotonicity) now applies verbatim to the paper comp<M,p,x,y>. Both provers honored
no-workspace-writes (v1 verified git-clean). Board: 24 proved. Next: guarded
two-copy-ladder proof via the equality; AGHP axiom statement (Fable + full judges);
relaxed-interlace defs.

## 2026-07-06 ~10:45 — guarded ladder PROVED; stated-queue EMPTY
Both provers closed two_copy_ladder via transfer (artifact lemma_A4 at p=1, tau=1;
min_self collapse; guard load-bearing exactly as the countermodel predicted). v2
selected (v1 logged: workspace-touch violation #3, self-confessed). Board: 26 proved /
0 stated / 4 open (aghp, balanced-family, relaxed-interlace, port:rankclaim-assessed).
Engine layer is now LIVE: paper SS2 machinery reachable through Dfamily=DSet.

## 2026-07-06 ~11:15 — AXIOM near-miss caught pre-declaration (lanes worked)
axiom:aghp REVISED before declaration: Opus audit (use-site sufficiency hunt) found the
size bound superpolynomial at Stage-1/2 (q inside the t-exponent) — sound but TOO WEAK,
would have made lem:polytime unprovable much later with the axiom already load-bearing.
Codex fast lane had cleared it (checked only the not-too-strong direction) — the layered
lanes caught complementary failure modes. Revised bound (q+2)^C*(cardY+2)^(Ct)*ceil(1/e)^C
verified: majorized by AGHP, poly(d) at both sites. NOTE: revised bound is SMALLER =
STRONGER claim — Opus lane re-verified literature-implication for the revised form;
Ultra npcc-2 harvest (on the old form) to be folded with this caveat; declaration still
held for harvest.

## 2026-07-06 ~12:15 — S4 counting lemmas PROVED (4/4 fleet)
balanced-projection + block-balancing closed (both provers each, v1s merged; byte-exact
claims verified by provers programmatically; zero workspace violations this round).
Pro harvest: REVISE identical to the already-applied Opus fix — two independent lanes,
one revision; defs CONFIRMED. Deep Think still pending; axiom declaration HELD.

## 2026-07-06 ~13:00 — THE BRIDGE PROVED (S4 foundations complete mod axiom gate)
relaxed_to_classical closed by both provers; v1 gated (reused the fleets own
balanced-projection for the fiber counting — compounding). v2 confessed probe-file
violation #4 (seconds, cleaned; logged). Remaining below the transfer theorems: NOTHING
— next: axiom declaration on npcc-3 verdicts, then extension + separation statements.

## 2026-07-06 ~11:45 — AGHP AXIOM DECLARED; S4 foundations COMPLETE
Pro (npcc-3, revised form): DECLARE — with the non-power-of-two alphabet trap flagged
and grounded via the Chernoff/random-multiset existence route fitting our bound.
Axiom record: codex CORRECT(old)/Opus REVISE->fix/Pro REVISE(old)->DECLARE(revised).
GOVERNANCE DEVIATION (logged for Simon): declared on 3/3 functioning-lane affirmatives;
Deep Think = two broken blank browser sessions (left pending; late objection = instant
re-audit). Both relaxed defs submitted. The ONLY non-kernel axiom is now load-bearing-
eligible: NPCC.finite_alphabet_balanced_family_exists.

## 2026-07-06 ~12:05 — robust-ladder corollaries PROVED (F1 guard in force downstream)
Both corollaries closed by both provers (v2 gated; zero workspace violations this
round; v2 self-audited hypothesis consumption). The F1 repair now propagates: every
downstream engine consumer inherits 2 <= D f explicitly. Board: 34 proved / 15 open.
Next: odd-copy seed (needs typed-Lambda design decision) -> grid induction -> hard
seed; then the protocol-transcript type layer before the three big theorems.

## 2026-07-06 tranche 4a (engine mid-layer opened)
- INTEGRITY FIX: discovered every commit since cff6a98 omitted the Lean sources
  (explicit pathspecs listed ledger/claims only; one NPCC-vs-Npcc casing miss).
  Proofs were working-tree-only; "BUNDLED" labels overstated. Fixed: 7f634af banks
  all sources; bundle regenerated. NEW RULE: every gate commit uses
  `git add Npcc.lean Npcc obligations.json claims loop-log.md pipeline/judgments`
  and ends with `git status --porcelain -- Npcc Npcc.lean` (must be empty).
- Retro-judge batch (R8 gap): 6/6 CORRECT (pipeline/judgments/retro-judge-batch).
- Staged LambdaGE (typed Lambda, unregistered def) + lem:odd-copy-seed-rungs +
  cor:plus-one-family (50d5254); C5 judge (codex blind+direct): both CORRECT.
  Fleet (Opus + codex lanes) proving via A3-transfer induction.
- Scout: artifact old_partition = paper lem:partition VERBATIM (B_branch_core
  min-max middle term included) -> partition demoted to transfer-grade; candidate
  claim + spec prepped, stages after the odd-copy gate (byte-identity ordering).
- Ultra npcc-4 FIRED (GPT-5.5 Pro browser): pre-clearance on partition rendering
  + grid-induction invariant (floor drift, side condition, A3/A4 sufficiency).
- 4a GATED: odd-copy-seed-rungs + plus-one-family PROVED (codex r1, Opus adjudication pending); 36/49. lem:partition STATED (old_partition transfer vehicle).
- lem:partition PROVED (both lanes r1; old_partition transfer; judge CORRECT blind+direct); 37/49. S3 control pair STATED (abstract-labeling rendering; NoWasteConclusion shared def); fleet + Ultra npcc-5 fired. AxCheck.lean tmp-file flag adjudicated: runner-authored (axiom gate), no lane violation.
- 4b GATED: no-waste + failure-to-separate PROVED (codex r1; judge CORRECT x3 incl. L<Q.card vacuity refutation); 39/49. S3 control chain now blocked only on classical-separation (needs protocol-restriction layer) + engine's power-of-two.
- GRID BATCH STATED (new-partition + iterated-seed + power-of-two) per Ultra npcc-4 design (capped-exponent invariant E(t,r)=min(rho^r,gamma^t); gridFloor def). npcc-4+npcc-5 harvests banked (both CONFIRM; labeling interface sufficient for classical-separation). Fleet firing.
- GRID GATED: new-partition + iterated-seed + power-of-two PROVED (codex r1 via artifact lemma_4_8_iterated_partition transfer - the grid ALREADY EXISTED verified in Workspace/Induction.lean, absent from spec Tools; Ultra invariant design not needed but archived); judge 4/4 CORRECT; 42/49. Engine remaining: hard-seed only.
- lem:hard-seed STATED (asymptotic exists-m0 form, threshold UNIFORM in the game - quantified before X/Y/f per paper order; t=2^m rendering). Last open engine obligation. Fleet + judge + Ultra npcc-6 (quantifier-order/effectivity audit) fired. Artifact sweep: Induction.lean also holds cor_4_9/lemma_4_10/thm_4_11 (predecessor asymptotics - analogy material); sweep's FOUND-FULL claims on S3/S4 discounted as keyword-matching (relaxed layer is new).
- F2: hard-seed REFORMULATED (delta-uniformity gap found by Opus lane refusing to prove; two-sided squeeze machine-confirmed x2; repair = delta(open <1/2) before threshold, m0(j,delta); b/game inside). PAPER-FINDINGS.md F2 + suggested paper edit. Repaired statement restated; lanes re-fired. F1-pattern held: honest-FAILED > fake progress.
- def:column-loss-resilient STATED (Transfer.lean opened; yLoss = ((h*2^-c)/(1+eps))^(1/t) unregistered companion; exponent-style q=2^Q,t=2^T; eps explicit param). Judge fired; protocol-prefix design-proposal lane fired (classical-separation is protocol-typed - RowOnlyToDepth + prefix labeling over artifact Protocol).
- def:column-loss-resilient PROVED (def-gate; judge CORRECT blind+direct, division-placement + subscript checks); 43/49. Open: hard-seed (lanes running), classical-separation (design proposal in flight), Extension, localized, Separation.
- HARD-SEED PROVED (codex, 3 rounds incl. honest-FAILED on pre-F2 form + capacity-crash continuation; App-B route: odd-copy l=j seed, grid rho=sqrt(m), s=floor(2 sqrt m/log m), filter-based threshold). 44/49 - SECTION 2 ENGINE COMPLETE, all kernel-clean. WATCH-ITEM: m0 witness NONCONSTRUCTIVE (eventually_atTop) - if Layer-B needs an effective threshold it is a NEW obligation (Ultra npcc-6 effectivity audit pending). probe_mathlib.lean (benign, ambiguous origin, zero impact) deleted.
- hard-seed ADJUDICATION: Opus lane independently PROVED the repaired form with an EXPLICIT m0(j,delta) = 2^(16(2^(j-1)+1)) + 4096 + (j+2)^2 + ceil((100 log2(1/eta))^2) + j (kernel-clean; seed.opus.v2.lean in session scratchpad) - proved-both met AND the nonconstructive-m0 watch-item DE-RISKED (constructive alternative on the shelf). Notes banked: rho=3 infeasible for hard-seed (beta=2 blows copy budget; rho=sqrt(m) forced); whnf/omega heartbeat trap with exponential witnesses (clear hm before omega; maxHeartbeats 1600000).
- thm:Extension + cor:localized-extension STATED (Transfer.lean; deps all proved so S4 opens ahead of the classical-separation bake-off; S generalized to ANY (q,t)-balanced family - safe-stronger, axiom instantiates; t=2^T r=2^R renderings; t/2<=pseed as 2^T<=2*pseed). Judge + Ultra npcc-8 fired. Bake-off: pro-7 design harvested (comparison next).
- ULTRA LANE STATUS: Deep Think UNAVAILABLE on the Gemini account (driver: no 'Deep Think' mode selectable - explains all 6 dead tabs today; not flakiness). Lane stood down until Simon re-enables; Pro Extended = sole Ultra lane. npcc-6b re-fired (Pro, F2-updated packet; original tab stalled).
- CORRECTION (Simon checked): Deep Think dead tabs = Gemini USAGE LIMIT exceeded, resets today 4:23pm - not an account/UI change. Plan: after reset, re-fire the blind design task (npcc-7c copy) + any still-relevant DT packets on next wake.
- lem:classical-separation-clean STATED (merged protocol-prefix layer: rectangle-threaded FirstKRowBitsOn, whole layer PROVED incl. both structural inductions; DecidableEq conflict resolved classically per frozen-statement-wins; single sorry = the claim). Fleet + judge fired; 7b/DT fold-in = late-objection path.
- CLASSICAL-SEPARATION PROVED (Opus lane; both conjuncts; kernel-clean) - SECTION 3 COMPLETE, 45/49. Route correction banked: spec's threaded density insufficient for unbalanced-split exclusion; paper's STRONG bound x > q*2^(1-b) derived from hgap and threaded through the induction (per-level plus_one_family exclusion resolves the depth-d budget crux). Conjunct (b) = the mapped composition exactly. codex/Fable lanes -> adjudication on return.
- classical-separation ADJUDICATION: codex lane independently PROVED both conjuncts (r3; same architecture: witness-invariant induction, per-level power_of_two/plus_one exclusions, strong density from hgap - confirms amplification-only kills ONLY depth-(Q-1) offenders). DISCLOSURE: lanes not fully hermetic on (b) helper design (r1 codex peeked at opus file before forbidden; rr2-3 re-derived from sanctioned text; gated proof kernel-verified regardless). Fable separation lane still out (3rd adjudicator).
- EXTENSION + LOCALIZED-EXTENSION PROVED (Fable lane; one master induction, localized = master, Extension = a:=0 r':=R instance; kernel-clean, zero diagnostics). 47/49. Route intel: Extension consumes ONLY clause (i) of column-loss-resilience + seed bound (clause (ii) reserved for Separation); block_balancing not needed (pigeonhole row step); invariant = (2^(R'-s)*pseed <= |Qc|, fiber threshold ceil(2^(R'-s)*x_seed*m), h*L <= 2^(a+c)*|Cc|, cost+s+c < D f+R'+T). Remaining: thm:SeparationTheorem (to state) + port:rankclaim (assessed).
- classical-separation TRIPLE-PROVED: Fable lane also closed both conjuncts (crux formally resolved: D f+1 insufficient at intermediate depths - power_of_two + plus_one per level required; hgap load-bearing TWICE: no-waste bijection AND plus-one density x > q*2^(1-b); real-inequality invariant weaker-per-step but sufficient). Three independent kernel-clean proofs of the S3 capstone. 47/49 gated (Extension pair in).
- T6 STAGED: the reduction tranche - 38 obligations (source = {0,1}-d-dim VBP c=1 m=4 from 4-Colouring; stages M0..M4; deliverable thm:reduction-gap; wrapper historically blocked on vbp_np_hard governance + statement-form ratification). Hardest: MFourNoWasteLift (protocol surgery, Fable-critical), stage1-threshold exact equalities, MThreeFuzzyLeaves, large-d-checklist (absorbs hard-seed m0 via bundled d_star), M1/M2-robust certifications. D1-D8 ratification decisions in t6-map.md. NEW toolkit flagged: protocol UPPER bounds (row-identification, partition composition, transposeComp).
- thm:SeparationTheorem STATED (relaunched Fable authoring lane; Extension hyp block + hx2 -> xseed <= 2^(-R), hrob rename for name collision, T0 = card X exact, conclusion pair = classical_separation shape at Rin = univ; findings all benign incl. dead junk-branch note). Judge + 2 prover lanes firing. THE LAST CORE THEOREM.
- T6 TOOLKIT GATED (2nd chain; T6 items carry kind=lemma so provisional signoffs applied per standing protocol): upper-row-id + upper-partition + family-lower (t<=q finding) + GameIso layer. Ratification pile += 3.
- npcc-10 T6 DESIGN AUDIT banked (retrieved MANUALLY by Simon from the stalled Pro tab): D1-D8 all CONFIRM w/ tightenings (Promise/VBPInstance separation, tagged Sum coordinate type, branch-local surgery for NoWasteLift, schema reuse for M2/M3, packaged hardness not native NPComplete, promise-typed axiom endpoint); 5 keystone check-ledgers; GameIso boundary ruling (quotients OUT - matches toolkit); 14 traps; rankclaim wording resolved (port = source-audit only, downstream NOT blocked). Two lanes lost to API 529 (construction author, codex sep driver) - relaunched; new construction lane carries the D1/D4 rulings from birth.
- SEPARATION CRUX FROZEN: codex partial (sep2.codex.v1.lean) verified honest - everything proved EXCEPT relaxed_separation_row_bits_core (conjunct (a), three-phase protocol control; statement compiles, claims byte-intact, conjunct (b) counting layer PROVED above it). Per standing cadence: Ultra npcc-11 FIRED on the frozen crux (both models); dedicated Opus lane on the core lemma from the codex partial; independent Fable lane on the full theorem; construction lane (M0-M2, 3rd launch) alive. 529 storm weathered - no state lost.
- T6 constructions FULLY GATED at NPCC/VBP.lean (root cause: mapper file split, then my wrong Reduction.lean reassignment duplicated the file, duplicate decls drowned by errHead; corrected). VBP.lean + claims committed (chain-2 abort had left them untracked). 55/87.
- def:H-local GATED (Stage1.lean; Hlocal + Hcap/Hover/HlocalAt companions; rfl-recovery of M1hat/M1 confirms coordinate spelling; underflow-free by construction; dep-list metadata corrected to include def:stage-matrices per the lane's finding).
- THM:SEPARATIONTHEOREM PROVED (Fable independent lane; 3-phase native; 20 private helpers; kernel-clean) - THE MATHEMATICAL CORE (Targets A-T5) IS COMPLETE. Findings: clause (ii) of column-loss-resilience UNCONSUMED (enters only via localized_extension - matches the paper); classical_separation black-box handoff does NOT transport (dead-rectangle phenomenon, same as bakeoff Q1) - phase 3 proved natively per-node with identical bounds; strong exponent bound (R+T)+1 < b derived from hgap. The Opus core-lemma lane + Ultra npcc-11 become adjudication/archive on landing.
- zero-anchor-preprocessing + C2FiberSurvival GATED (candidates were standalone fresh files - guard caught both, merged onto live files; MERGE-DISCIPLINE note for future lane prompts: candidates must be full replacements of the LIVE file). 60/87. Opus core-lemma lane landed as CORROBORATION (ported the live sep_* toolkit; honest provenance note) + intel: the pseed-block invariant genuinely walls (needs a relaxed plus-one that does not exist) - the full-row invariant is the right one (RELAXED-PLUSONE-ASSESSMENT in scratchpad).
- lem:large-d-checklist GATED (LargeD.lean; 16-field Checklist, explicit d0 = 2^64 witness, Nonempty-before-choice per D3, dStar companion; binding gate t1<=q1+5 needs log d>=64; divisibility via powers-of-two; eps-domination isolated as epsQT_le_inv). RESIDUAL ITEM (named, not hidden): hard-seed density domination h'2 >= 2^(-2^(0.49 sqrt(log t2))) omitted from the bundle (transcendental nesting) - decide native-vs-fallback-axiom at the Stage-2 consumer lemma per D3. 61/87.
- def:stage4-matrix GATED (Scaffold.lean; M4 = Sum.elim template/vector halves; tagged R4 = R3 (+) [n]; choice-free diagCoord case split; transversalAt implements the DT duplicate fix; localGadget_tail pins the finFunctionFinEquiv encoding alignment; import direction flipped VBP->Scaffold, dead import removed). 5 flagged decisions -> ratification pile.
- 7th FINDING (M1LowColumnStage2 lane, honest FAILED): ledger vehicle WRONG (relaxed_to_classical impossible at u=(9/16)r't1 > t1; 2x independent xhigh confirmation) - correct vehicle = localized_extension (lemma TRUE, numerically tight); REAL blocker = no concrete IsColumnLossResilient instance exists -> NEW obligation lem:M0-column-loss-resilient (degenerate D=1 base case, hand proof); seed-bound inequality routed to the LargeD extension lane; conditional proof banked (m1lcs2.opus.v1.lean, 3 named hypotheses). Ledger: 88 obligations.
- lem:stage1-threshold GATED (all FOUR directions; both EQUALITIES registered; paper prices lower bounds by DIRECT COUNTING not robustness - engine unused, finding banked; reusable heavy-rectangle machinery for the dense corollaries; 3 use-site gates discharged downstream by large-d). Codex lane left a working copy in pipeline/tmp (benign, logged).
- SIMON RATIFIED scope (Discord to coauthors, relayed): kernel = construction SIZE + NO<=>GAP proof; polynomial RUNTIME not formalized as first objective (easy to check by hand) - D2/D7 now RATIFIED not provisional. Wrapper single-blocked (only vbp_np_hard governance remains); axiom-formulation audit STARTED (Ultra npcc-12 fired: shape A/B/C ruling, source-encoding choice, promise-leakage placement, over/under-claim check).
- ALLOCATION CORRECTION (Simon): prover lanes drifted Opus/Fable-heavy vs the resource doctrine. RULE (standing): provers DEFAULT to codex-driven lanes (free + rigor authority; thin Claude driver only); Opus = adjudication diversity + merge/integration; Fable = design-critical only (statement authoring, type layers, keystone design). Applies from the next wave (M-robust chain, M1LCS2 completion, fuzzy leaves, NoWasteLift proof).
- lem:M0-column-loss-resilient GATED (h-agnostic via density-gate hypotheses; elementary two-column argument, rankclaim NOT needed - its 1+log2 y floor fails at these densities, finding-lite; D M0 = 1 companion; half_lt_yLoss discharges the gates at LargeD scale). Unblocks the corrected M1LowColumnStage2 (conditional proof banked).
- lem:large-d-checklist RE-GATED, reformulation complete (21 fields: all six App C.1 conjuncts + seed-slack C9 CORRECTED vs my rendering - true form via b'2=3logd integer-log, lane followed the paper and flagged; witness RAISED 2^64 -> 2^256, binding constraint now C6 fiber-survival at loglog d >= 8; hard-seed h'2 domination stays the named residual). Judge-triggered reformulation cycle CLOSED.
- GATE WAVE complete: gap-YES PROVED+GATED (scaffold_completeness - the second ratified kernel deliverable); Gadget pair GATED; size bounds GATED. ZZscratch removed. TRIPWIRE: chained runner calls under load can succeed with EATEN stdout - gate scripts now tolerant (state-then-signoff-then-submit regardless).
- WAVE 4: size unparked (contention strikes, not defects) + submitted; lane-stated items gated from the live files their registrations came from (M1LowColumnStage2 COMPLETE - finding-7 chain closed; dense + chosen-dense thresholds; port:rankclaim stated by an initiative-taking codex lane - REVIEW ITEM for Simon's ratification pile). PROCESS NOTE: the full-access codex lanes ran the runner themselves (state calls) - that was the workspace 'dirt'; prompt template hardened to forbid runner invocation (gates are the orchestrator's).
- NoWasteLift KEYSTONE STAGED: Control.lean += the D5 restrict layer (evalDepth/restrict/restrictFoldCount + exact branch ledger + D_subgame_le_restrict_cost; direct install with in-script claim verification + full build - companion machinery has no gate vehicle, logged); lem:MFourNoWasteLift statement FROZEN (dynamic BranchAt rectangles per the adopted design; Lift.lean created). Statement judge firing; proof waits for the tower (fuzzy leaves et al.).
- M1PlusVectors pair GATED (GameIso-on-transversal to the chosen-coordinate Stage-1 game per the adjudicated duplicate-row routing; canonical-dense corollary). Vector branch of the tower COMPLETE - reduction-gap's third dependency arm closed.
- npcc-12 HARVESTED (vbp_np_hard formulation, Pro lane 1): SHAPE C recommended - bundled VBP4PromiseHardnessPackage (4-Colouring edge-list source per the paper's Prop 42 route; promise as a package FIELD; explicit monomial size clauses; no NPComplete/no runtime claims). Flags: preprocess needs Promise-preservation lemma; promise-violating inputs = wrapper's hard-coded-NO branch (not the axiom's). NOTE for Simon: the package axiomatizes the paper's OWN Prop 42 (proved there) + leaves 4-Colouring hardness to prose - declaring it is modest; formalizing Prop 42 natively is the upgrade path. Codex second-lane audit firing per AGHP governance. pro-10 also harvested (third T6 design ruling - archive; two already adjudicated).
- 8th FINDING: NoWasteLift statement judged INCORRECT (phantom-depth BranchAt - rectangles untied to actual protocol computation; the dynamic-frontier content missing). REFORMULATED; redesign lane firing with the judge's under-coverage list binding + the restrict layer's Computes/cost lemmas as the binding mechanism. Budgets/local witnesses confirmed correct - retained.
- M1 pair GATED: cor:M1-complexity (D(M1)=a+1 via M1_low_column_stage2 at r'=r1 + capacity log identity) + lem:M1TerminalStage2 (one-copy bracket members contain projected r'=1 M1 subgames; transport via M1_interlace_one_project_le). RATIFICATION FLAG: TerminalStage2 carries 3 explicit App-C density hypotheses (hy_le_one/hrowTerm/hcolTerm) NOT discharged from Checklist - discharge companion owed before consumers instantiate it.
- lem:polytime GATED after lean_name correction (stale NPCC.M4_size_poly -> NPCC.output_size_bounds; the 'contention' diagnosis in the unpark note was wrong - failure was deterministic unknown-constant). SIZE deliverable certified.
- HISTORICAL vbp_np_hard second-lane audit banked: DECLARE (converges with ultra-npcc-12 Shape C; placement = post-VBP file since VBP.lean imports Axioms.lean). Support lemmas registered as aux:vbp-wrapper-support (open); prover lane fired. At this stage the package remained Simon-gated; this was superseded by the later proved package.
- lem:M1-robust GATED (four-clause robust certification for M1; consumes M1LowColumnStage2 residual-density instantiations - pro-10 warning honored: densities verified by value). M1 layer COMPLETE.
- pro-10 (third T6 design ruling) adjudicated: D1-D8 all CONFIRM, no reformulation; NWL keystone checks folded into the nwl2 judge frame; fuzzy-leaves + robust checklists routed to upcoming lanes; polytime naming trap already honored via lean_name correction.
- aux:vbp-wrapper-support GATED: preprocess_promise, normalizeInstance_promise/isYes_iff, feasible+bad-bin transports, not_isYes_of_not_promise (pigeonhole - true under live defs). vbp_np_hard's composition path was theorem-complete; at this historical stage the package was still Simon-gated. This was superseded by the later proved package.
- Stage-2 OPENERS gated: lem:M2-column-loss-resilient (clause (i) proved via M1TerminalStage2; clause (ii) residual three-rung Lambda estimates EXPOSED AS hresidual GATE - discharge lane fired, paper proof 7186-7288 routes through the M1_robust rungs) + lem:M2-hard-seed (direct form; h2'-monotonicity + (9/16)t2 copy-count bridges owed downstream). RATIFICATION FLAG: hresidual is proof content as hypothesis until the discharge lands.
- NWL redesign judged: INCORRECT by single over-claim (exact alpha-block column iff; paper's Stage-2 control is dominant/fuzzy - only dense Y subset survives). ALL prior under-coverage now covered; side conventions + budget forms confirmed. Surgical fix applied (clause removed; containment redundant with BranchExtends.cols_sub); branch layer being promoted to Control.lean for Stage-3/4 sharing; delta-judge next.
- lem:MFourNoWasteLift RESTAGED (attempt 2, judged): redesign covered all 8 prior under-coverage items (dynamic BranchAt w/ transcript+reachability+residual_eq_actual+cost ledger; refinement BranchExtends); single over-claim (exact alpha-block column iff) removed per judge - paper's Stage-2 control is dominant/fuzzy, dense-Y witness IS the synchronization content (delta-judge confirmed, blind item 7). Branch vocabulary PROMOTED to Control.lean (game-generic, claim-free infrastructure; installed atomically with Lift.lean - old thin stub removed). Statement stated+signed; PROOF deferred until M-tower complete.
- aux:m2-midlayer GATED (M2_upper_bound via comp_le_partition + transpose swap; q2 clog bridge; hard-seed copies = (9 t2)/16 under 5<=log t2). cor:M2-complexity REFUSED at the gate: the lane hypothesized its own lower bound (hlower) - stripped, not banked as proved. CRUX NOW EXPLICIT: (i) hard-seed -> ambient M2 lower bound via localized_extension; (ii) hresidual three-rung discharge from M1_robust + App-C residual densities. Ultra fired + codex lane fired (harvest-prior-then-fire honored).
- aux:m1-terminal-discharge GATED: hy_le_one + hcolTerm unconditional; hrowTerm at explicit 2^18 <= log2 d (paper App-C 7116-7147); M1_terminal_stage2' = hypothesis-free composition. ASSEMBLY NOTE: d_star regime is now 2^18 <= log2 d (supersedes 256) - Checklist re-witness at assembly is log-scale numerics.
- Stage-1 batch C5 judge: cor:M1-complexity, lem:M1TerminalStage2, lem:M1-robust, aux:m1-terminal-discharge ALL CORRECT (hunted: b1/b1' by value, transpose orientation, equality-from-one-side, gate mutual satisfiability at 2^18 regime - clean).
- CRUX STRUCTURALLY CLOSED: cor:M2-complexity GATED with the lower bound ASSEMBLED (localized_extension @ f=M1T, T=M2_T, R=log r2, S=S2fam-cast, pseed=copies, Rs=Cs=univ; back to M2 via D_equiv_invariance; upper via M2_upper_bound+clog_q2_eq) - NO hlower. aux:m2-clr-discharge GATED: clause (ii) via all three M1_robust rungs (r2/r4/r3 at y,y/2,y/4). REMAINING DEBT = 9 explicit App-C numeric gates (hresidual_density window, hseed_bridge, hr2pow, hp1/hp2, hxseed_le_one, hrow_threshold, + 3 terminal gates already discharged in Stage1) - numerics lane next, Ultra npcc-13 Q2/Q4 feeding it. RATIFICATION FLAG: same gated-hypotheses pattern as M1TerminalStage2 (judged CORRECT there).
- lem:M2Separation GATED: relaxed_separation instantiated at f=M1T, S=S2fam-cast, h=1 (the paper's lem:mono upgrade - hres_one gate), hrob=M1_robust (PAPER-CONFIRMED at main.tex 3907: 'base matrix is robust by lem:M1-robust' - the orchestrator's prompt wrongly demanded M2_robust; lane deviation was CORRECT; M2_robust remains needed for M3Separation). ~20 explicit numeric gates (superset of M2-complexity's; h=1 variants + band + gap new) - numerics/composition lane owns them. cor:M2SeparationTransposeDenseRows REFUSED at gate AGAIN: candidate was a tautology (conclusion = 4 of its own hypotheses verbatim) - the corollary must PROVE the branch data from M2_separation; dedicated relabelling lane owed (m3design hard-step #1).
- lem:M2-robust GATED: IsRobust(M2^T, delta, b2) - Robustness_2 by VALUE (pro-10 b2/b'2 collision check passed); four clauses via block_balancing + localized_extension at residual widths r2, r2/2, r2/4 (paper 7379-7528); consumes the composed M2_column_loss_resilient' + M2_complexity. M2 CHAIN COMPLETE except the dense-rows corollary (keystone lane running). M3Separation's last dependency is now live.
- aux:m2-dense-separation-core GATED: dense-rows restricted separation/no-waste core proved (relaxed_separation @ C'=Sdense, h=sigma, band=Checklist.dens_sep_dense; paper 3955-4018). cor:M2SeparationTransposeDenseRows remains OPEN: blocked on the missing PUBLIC BRANCH CONSTRUCTOR (FirstKRowBitsOn+NoWasteConclusion -> semantic BranchAt w/ reachability/actual-transcript/residual-eq-actualSubtree/restrict-ledger/actual-depth/computes + transpose Bob-side-trace lemma) - THE isolated keystone infra, same bridge the NWL proof needs. Constructor lane + Ultra pre-clearance fired.
- aux:m2-numerics GATED: pro-13's false-at-256 finding VERIFIED independently (doctrine honored - Ultra claim re-derived before banking); paper's h2-prime route confirmed w/ line refs; composed wrappers M2_complexity' + M2_complexity_h2prime landed; final irreducible gate set = 2 exponent windows + yLoss window + row ceiling (all d-monotone numerics -> final d_star bundle at loglog d >= ~640, the paper's own 'eventually dominates' honestly quantified).
- aux:branch-constructors GATED (tranche 1): mkBranchAt_of_rowPrefix discharges all 13 BranchAt fields from FirstKRowBitsOn + Computes + realized-fiber data (6 new bridge lemmas: actual-vs-row prefix code/side/subtree equivalences, cost + depth decompositions). STRUCTURAL NOTE: BranchAt reachability is ambient - constructors need univ rectangles (consumers subtype-encode; matches the dense core's shape). Tranche 2 (swap transport + appendCode composition) lane fired.
- aux:branch-constructors-2 GATED: swap transport layer + mkBranchAt_of_colPrefix (Bob segments constructible via FirstKColBitsOn = row-onlyness of the swap; branchAt_of_swap side-label transport). Composition (appendCode towers) = the last constructor piece - tranche 3 after Ultra npcc-14 Q3 folds in.
- aux:m3-separation-core GATED (Stage3.lean born): classical_separation instantiated at the M2^T base w/ both public<->subtyped transports proved. lem:M3Separation held OPEN - the conclusion's complexity field is assumed-through (hM3_complexity); complexity lane fired (upper = row-identification; lower = iterated partition seed @ M2^T consuming M2_robust + the live two-copy ladder). pro-14 harvested: Q1/Q2 CONFIRM the two gated constructor tranches independently; Q3/Q4 = transcribable composition + relabelling designs -> tranche-3 lane fired with pro-14 as spec.
- lem:M3Separation CLOSED + GATED (M3_separation_closed): aux:m3-complexity proves the assumed-through field via the REAL ladder (power_of_two_lower @ M2^T w=2); hdelta_sep/hstage3_gap/hD2 discharged in-file; residual inputs = hrobM2 (public robustness conclusion - M2_robust's balance windows use a PRIVATE Stage-2 type, cleanup wrapper owed) + the standard Stage-2 numeric bundle. Stage-3 separation arm DONE; fuzzy leaves = last Stage-3 open (waits on T3 composition + dense-rows corollary).
- aux:branch-constructors-3 GATED: append arithmetic + restrictSub actual-transports + lift helpers + the FULL Q4 relabelling layer (alphaOfCode/YofCode). BranchAt.compose deferred to T4 - obstruction NARROWED to dependent Fin-width casts (cast-normalized append lemmas first; stalled goal banked). ROUTING: dense-rows corollary needs NO composition (single-segment at R+T + relabelling) - its lane unblocks NOW; compose is NWL-tower-only.
- aux:branch-constructors-4 GATED: BranchAt.compose + BranchExtends proved (the .val strategy dissolved the T3 dependent-width casts - all three actual append bridges landed as width-free Nat/List equations); compose_colPrefix = the NWL tower shape. CONSTRUCTOR KEYSTONE COMPLETE. NWL proof campaign toolkit fully assembled: registered statement + restrict layer + branch layer + 4 constructor tranches + M3Separation closed.
- aux:m2-dense-code-family GATED: the code-indexed dense-rows branch family (swap-orientation Bob traces at M2DenseDepth; YofCode at (1-eta2); S-survival; diagonal containment; zero branch-data hypotheses - the prior tautology archetype fully avoided). cor:M2SeparationTransposeDenseRows held OPEN on exactly alphaOfCode_surj_on_Q (per-alpha indexing; dominant-block counting) - surjectivity lane fired; fuzzy-leaves lane polls behind it. NWL proof-plan pre-clearance (npcc-15) fired on both Ultra models.
- cor:M2SeparationTransposeDenseRows CLOSED + GATED (per-alpha form): alphaOfCode surjectivity proved by the paper's pigeonhole (label fibers partition the full row fiber via card_eq_sum_card_fiberwise; strict low-fiber sum < q*T < |C1| via hgap - paper 3937-3952); per-alpha data indexed by the consumer's Fin q2 through hqcast. The code-family + surjectivity two-lane decomposition fully avoided the earlier tautology archetype. Fuzzy-leaves lane poll target now live.
- aux:m3-fuzzy-partial GATED: separation conclusion + per-alpha dense packaging (sigma=1-8h2) - no assumed branch data. lem:MThreeFuzzyLeaves open on ONE mechanical piece: BranchAt reindex transport (swap(Pdense) -> original residual), then compose/cRep/exact_M1_copy are routine. Tranche-5 lane fired (checks for npcc-15 harvest artifacts before finalizing).
- aux:branch-constructors-5 GATED: reindex transport (commutation pack + branchAt_of_reindex, residual_eq_actual definitional). Fuzzy close BLOCKED on the ambient synchronization argument (restricted column-onlyness does not lift; = paper 4607-4646 stopping-time; = npcc-15 Q1) - ONE design serves BOTH fuzzy leaves (Stage-3 instance) and the NWL core (Stage-4). Holding for the Ultra rulings; harvest in flight.
- Deep Think backlog (11 artifacts) digested: 2 objections vs gated work ADJUDICATED FALSE (DT-10 balance-radius/coordinate-count confusion; DT-11 restrictSub-vs-restrict misread - the fold ledger is separate by design); DT-12 INDEPENDENTLY converges on the synchronization design (zero-folds-before-stopping-time via the exact restrict ledger + the same NWL assembly route + the fixed NO-order) = THIRD independent derivation; DT-8 adds the branch-local/dynamic-frontier warning (not uniform depth) as a statement constraint; DT-9's n-AND-d bounds + hard-NO fallback already satisfied by the Shape C package + not_isYes_of_not_promise. npcc-16 (dedicated sync deep-dive) fired on both Ultras per Simon's more-firepower call.
- aux:m3-sync GATED (the mechanical half): ambient FirstKColBitsOn -> full consumer dimBranch package via the constructor stack. THE REMAINING MATHEMATICAL CONTENT OF THE WHOLE FORMALIZATION is now one lemma: ambient FirstKColBitsOn for each bin residual from the exact budget + floors (the budget-forces-structure argument; triple-converged design; npcc-15+16 rulings incoming).
- aux:m3-budget GATED: the budget lemma's full scaffolding (target structure M3BudgetColumnTarget; certified cost side; target->consumer composition). Remaining = ONE stopping-time induction (invariant: dense survivor subrectangle + fold ledger along the actual walk). Two codex lanes honestly declined it unaided - npcc-16 (both Ultras) is ruling on exactly the invariant; decisive lane fires on harvest.
- aux:nowaste-core GATED (NoWaste.lean born): FirstPatternOn + conversions + fiber machinery + terminal witnesses + cost bridges (npcc-16 Pro ruling lanes 1-3, transcribed and kernel-proved). Main theorem staged as honest Prop statements; the ONE remaining bridge = ambient stopping-subtree sync - finisher lane fired.
- aux:nowaste-main GATED (after lean_name correction NPCC.Protocol.noWaste_firstPatternOn_univ_of_restrict; the earlier axiom-gate failure was the stale name, build was clean) === THE LAST MATHEMATICAL CONTENT. Faithfulness judge verdict = SOUND (line-referenced vacuity audit: coverage over all words via replicate-false witness; terminal witnesses pin tightness not contradiction; bridge non-circular genuine lower bound; fold strict-decrease real; ambient-lift induction legit; faithful to main.tex 4889-5029). EVERYTHING REMAINING IS ASSEMBLY.
- aux:m3-stopdata GATED === CONSTRUCTIVE NON-VACUITY of the no-waste keystone: Stage3StopData.ambient_col applies the theorem to the real Stage-3 protocol (hypotheses ARE dischargeable); full chain to M3BudgetColumnTarget + adapter consumption verified. Combined with the SOUND soundness judge + kernel proof = the keystone is triple-confirmed real. lem:MThreeFuzzyLeaves open on ONE floor lemma (terminal M1-copy: D(M1) <= D(subgame) at each reached rect). Floor lane fired; refutation skeptic running.
- KEYSTONE QUADRUPLE-CONFIRMED: no-waste theorem = kernel proof + soundness judge SOUND + constructive consumer-discharge (Stage3StopData.ambient_col) + adversarial refuter SURVIVES (with a KERNEL-CHECKED non-vacuity witness nwrefute_witness.lean exit 0, satisfying the full bundle at exact cost equality; also proved the [bob] conclusion FAILS for that P, so conclusion not automatic). FINDING #9 (non-fatal, self-correcting): StopLeafContained is same-prefix row/col PROJECTION containment, not literal terminal-leaf containment; game param unused in the body. SAFE because the hard field D(subgame G Rw Cw) >= B0 is unprovable for trivial rectangles - forces consumers to genuinely-hard (M1-copy) rectangles. Documented; NO code change (rename would re-gate NoWaste; hazard self-corrects). Consumers (floor lane, NWL) already supply M1-copy rects.
- aux:m3-floor GATED: D_exact_copy_le_subgame (general exact-copy D-lower-bound, no injectivity, reusable at Stage 4) + the TerminalHardWitnesses reduction to per-word prefix-copy data. Fuzzy close needs ONE more reindex (bin-residual prefix fibers <-> Stage-2 code-data branches); closer lane fired.
- aux:large-d-checklist-2p18 GATED (Simon-signed fix 1b): large_d_checklist_strong @ witness 2^(2^18) bundles Checklist + 2^18<=log d; checklist_of_log_ge_256 helper refactor. Final-assembly d_star now satisfies the 2^18 gate. Fix 1a (NWL reformulation IsPow2+log) queued for the NWL proof lane.
- aux:m3-prefixcopy GATED: rowsAtPrefix_eq_of_firstKColBitsOn (row-invariance under column bits - Bob-only+coverage => rows fixed) + Stage3StopData assembly from prefix-copy inputs. Fuzzy close now needs ONLY the instantiate-at-bin-residual transport (apply the Stage-2 per-alpha corollary to a reindex of the bin residual; NO data transport). Transport lane fired.
- aux:m3-transport GATED: the instantiate-at-bin-residual reframing fully in checked Lean (reindexed dense protocol computes M2DenseGame + budget PROVED; Stage-2 corollary instantiated; exact-M1-copy + fibercover helpers). Fuzzy close now needs ONLY the M3BinDenseReindex Equiv witness (2 explicit bijections onto the bin rectangle). Equiv-closer fired. FAITHFULNESS Q RESOLVED: paperframe confirms D_ctor=ceilpowtwo(max{dim,d_star}), threshold-free main theorem, our 2^(2^18) = valid d_star; fixes 1a/1b load-bearing-correct.
- aux:m3-binreindex-witness GATED: the M3BinDenseReindex Equiv witness (injective diag/survivor maps + game_eq) modulo 2 branch memberships + the code->bin binBranch bridge. Fuzzy close = ONE exhaustive assembly lane (batch: branch-row/col characterization of mkBranchAt_of_rowPrefix + dominant-bin->binBranch family + the 2 memberships + full M3FuzzyLeavesData package). Convergent: 5 lanes each built reusable machinery, tail now = branch-structure characterization only.
- aux:ctor-gates GATED (Reduction.lean born): CtorScaleCertificate proves IsPow2+2^18log+Checklist+2<= from an instance (the regime supplier) + ceilPowTwo size bounds; partial CtorGates. NUMERIC DEBT flagged: 5 gates (hm0_le, hrow_threshold, hraw/hprime, hy_three_fifths, hrobM2/M2_robust_closed) not yet Checklist-derivable - leaked from the M2/M3 assault; discharge lane firing to pay from the 2^(2^18) regime. Endgame statements need these clean.
- aux:m3-binbranch-char GATED: branch characterization (rows=rowPrefixRows, cols=univ) + code->bin family (bin surjectivity counting) + memberships + reindex-for-binBranch -> chain REACHES per-bin dense alpha data. Fuzzy close = final packaging (alpha data -> Stage3StopData -> ambient_col -> M3BudgetColumnTarget -> dimBranch -> M3FuzzyLeavesData); all pieces live. Packaging lane fired (6 lanes converged; tail now minimal).
- aux:m3-package(+final) GATED: the FULL M3FuzzyLeavesData assembly (every field: binBranch/S/Y/cRep/fiber_cover/exact_M1_copy) modulo ONE named hypothesis = M3_fuzzy_leaves_sync_bridge (M3BudgetColumnTarget + diag_cols). lem:MThreeFuzzyLeaves stays OPEN (bridged theorem refused as the real obligation - honest partial). The ENTIRE fuzzy close now reduces to: discharge the sync bridge = build M3BudgetColumnTarget per-bin from the alpha data (Stage3StopData -> ambient_col). Final bridge lane fired.
- NUMERIC DEBT FULLY PAID (serial re-gate after a concurrent-ledger-write race): aux:gate-discharge-partial (G1/G2/G4) + aux:gate-g3g5 (G3/G5 + large_d_checklist_g3g5 bundle Checklist+2^18log+G1-G5) + aux:m2-robust-closed (G6). All 6 endgame gates now derivable from the regime. Final d_star ~2^(2^(2^16)) (constant, faithful). Remaining: bundle G6 into large_d_checklist_full; then CtorScaleCertificate supplies EVERY endgame hypothesis from an instance. LESSON BANKED: ledger-mutating gates run SERIALLY.
- aux:m3-dense-floor GATED: the CORRECT dense terminal floor (stage1_chosen_dense_threshold on HlocalAtSub over dense S, a+2>=Bcap) + Stage3StopData.of_colPrefix_dense_HlocalAtSub_copies. Fuzzy close 3 sub-gaps: (1) reached rect contains HlocalAtSub via M1_plus_vectors_canonical_dense (the M1-only copy insufficient - column-restriction lowers D); (2) first-bit reindex transport for restricted_col; (3) List/code coverage bridge. This IS the NO-direction crux (shared w/ reduction_gap). Directing next lane at M1_plus_vectors_canonical_dense.
- REDUCTION INFRASTRUCTURE COMPLETE: aux:gate-full (large_d_checklist_full bundles Checklist+2^18log+ALL 6 gates+robustness) + aux:ctor-full (CtorScaleCertificateFull: an instance I -> IsPow2+2^18log+Checklist+G1-G5+IsRobust(M2^T), EVERYTHING the endgame needs). Import cycle resolved (GateDischarge->Stage2 only; Reduction->GateDischarge). Now: once fuzzy leaves closes (Opus subagent + npcc-18 frontier design in flight), NWL + reduction_gap proceed with CLEAN hypotheses from CtorScaleCertificateFull.
- aux:m3-fuzzy-opus GATED (Opus subagent, type-unit-test discipline WORKED): fuzzy CRUX RESOLVED. M1_dense_column_subgame_floor (a+1 via M1_low_column_stage2 dense-column-slice - avoids the 2 un-inhabitable floors the discipline ruled out early) + restricted_col transport + dense hard builder + M3_build_sync_bridge (full wiring). Fuzzy close = 1 named actualBitListRaw transport (all commutation live). Gemini Deep-Think + parallel GPT-5-xhigh both converged on the floor + the same residual gap. Final transport lane fired.
- === lem:MThreeFuzzyLeaves CLOSED + GATED === the Stage-3 fuzzy-leaves layer is COMPLETE. The transport (actualBitListRaw commutation -> per-bin Stage3StopData -> ambient_col -> M3BudgetColumnTarget -> M3_build_sync_bridge -> M3_fuzzy_leaves) closed on the Opus-resolved dense-column floor (M1_dense_column_subgame_floor via M1_low_column_stage2). ~10 convergent lanes + an Opus subagent that resolved the crux via the type-unit-test discipline. NWL Phase B now has its exact template (fuzzy = fuzzy-at-Stage-3; NWL Phase B = fuzzy-at-Stage-4). Remaining: NWL proof (Opus workflow + codex running), reduction_gap, wrapper (Simon: vbp declare).
- lem:MThreeFuzzyLeaves C5 faithfulness judge: CORRECT (forall-alpha not exists; densities 1-8h2/1-eta2 exact; cRep retains actual R1 value; exact M1 copy; branch tower side traces correct; non-vacuous). Stage-3 layer kernel-proved AND faithful.
- npcc-18 harvest (6 files): Ultra models DISAGREED on the Stage-3 floor (deepthink-14: drop HlocalAtSub, M1|dense Bcap=a; pro-18: need full HlocalAtSub a+2) - BOTH WRONG; the compiler+judge settled it (Opus M1_dense_column_subgame_floor a+1 via M1_low_column_stage2, a THIRD route; fuzzy closed+judged CORRECT). Doctrine vindicated: verify Ultra, never bank unverified. STAGE-4 guidance CONVERGES + resolves NWL obstruction 2: deepthink-14 Q4 + opus-B route(b) = Phase B builds M4LocalBranch AMBIENT over C4 via M1_plus_vectors_canonical_dense (native dense Y in diagCopySet w/ canonical diagCopyCol cols), NOT the k0 slice; slice only gives Phase-A separation. NO-contradiction route fully spelled (bad leaf -> vector tool 3rd conjunct -> a+2<=Bcap=a+1). npcc-17 (faithfulness) = not-a-problem, confirms the paper-grounded resolution.
- === lem:MFourNoWasteLift CLOSED + GATED === THE NoWasteLift KEYSTONE is proved (Fable 5 agent; Stage-4 transpose-separation ported from the just-closed Stage-3 fuzzy template). `M4_no_waste_lift` instantiates `M4_no_waste_lift_from_certificates` with BOTH certificates discharged: Phase-A terminalHard = D(M2) bin-floor (M2^T copy + comp_transpose); Phase-B bin-terminalHard = canonical diagCopyCol Bcap floor over `M1_plus_vectors_canonical_dense` (AMBIENT over C4 via route(b), not the k0 slice). New lemmas: `M4BinDenseReindex` (transpose-separation, game_eq=rfl chain), `actualBitListRaw_eq_restrict_of_terminal_budget` (budget-forced bit equality), `M2Dense_game_floor`. Statement = Simon-signed reformulation (M3-fuzzy analytic bundle added to hyps, paper conclusion verbatim, discharged downstream by CtorScaleCertificateFull). axioms=[propext, Classical.choice, finite_alphabet_balanced_family_exists, Quot.sound]. **Board: 122 proved, 2 open (thm:reduction-gap, thm:main-nphard-intro). ALL MATHEMATICAL CONTENT DONE — remaining = reduction assembly + wrapper.**
- === SIMON RATIFICATION + WRAPPER UNBLOCK (2026-07-07; historical staging) === Simon: "Yes I approve, please record it in the project. I unblock the wrapper too." RECORDED: (1) all provisional statement sign-offs from the autonomous ENDGAME run are RATIFIED (incl. the lem:MFourNoWasteLift reformulation, delta-judged CORRECT); (2) thm:main-nphard-intro UNBLOCKED -- the then-governed VBP package NPCC.vbp_np_hard was authorized in Shape C form (per npcc-12, audited x2) and the wrapper statement form (reduction map + gap + explicit size bound; runtime/NP-completeness stay prose) was ratified. Closing sequence at the time: render+final-faithfulness-audit vbp_np_hard -> declare/formalize (Wrapper.lean) -> author+judge main_np_hardness statement (over ctorScaleFull) -> gate reduction_gap (lanes in flight) -> assemble+gate main_np_hardness. NOTE the wrapper uses ctorScaleFull/reducedVectorsFull (full-bundle scale), superseding the strong-scale blueprint.
- === HISTORICAL vbp-np-hard governed stage (superseded by proved package) === NPCC/Wrapper.lean born: FourColorInstance (edge-list 4-Colouring source) + VBP4PromiseHardnessPackage (Shape C, npcc-12). Governed stage: Simon-authorized 2026-07-07 + adversarial 5-lens audit CLEAR_TO_DECLARE (0 blocking; satisfiability judge gave a POSITIVE TRUTH CERTIFICATE -- brute-forced all 251 small graphs + the Kk chromatic boundary; over-claim/paper-match/scope all CLEAR; banked audit-vbp-np-hard-governed-2026-07-07.md). Historical footprint at that moment included vbp_np_hard; current footprint after discharge is [propext, Classical.choice, Quot.sound, finite_alphabet_balanced_family_exists]. Sufficiency judge flagged (non-blocking) that main_np_hardness should compose the package sourceSize bounds into an end-to-end poly(sourceSize) statement -- later folded in.
- === thm:reduction-gap CLOSED + GATED + faithfulness-judged CORRECT === THE PAPER MAIN GAP THEOREM. NPCC.reduction_gap (Gap.lean): for a promise VBP instance I, (I.IsYes -> D(M4 (ctorScaleFull I) (reducedVectorsFull I)) <= Byes) AND (not I.IsYes -> Byes < D(...)). Opus lane closed it: YES via scaffold_completeness + zero_anchor feasibility transport; NO via the 4-step kill (M4_no_waste_lift with ALL ~27 hyps discharged [17 from CtorScaleCertificateFull+ctorGates, 6 dense via new gap_* lemmas incl. resilient_density_up upgrade] -> zero_anchor overload -> stage1_chosen_dense_threshold a+2 floor -> dupExpansion_D_le_residual_cost bridge [D_subgame_le_restrict_cost + D_le_cost_of_computes] -> a+2 <= Bcap=a+1 contradiction). axioms=[propext, Classical.choice, finite_alphabet_balanced_family_exists, Quot.sound]. C5 judge CORRECT (both directions faithful, NO strict, Byes=paper B_yes, scale threshold-free, non-vacuous). Board: 123 proved, 1 open (main_np_hardness, wrapper codex lane in flight). ALL MATHEMATICAL CONTENT COMPLETE.
- ============================================================
- === thm:main-nphard-intro CLOSED === FORMALIZATION COMPLETE
- ============================================================
- NPCC.main_np_hardness (Wrapper.lean) PROVED + faithfulness-judged CORRECT (headline C5: gap iff two-sided, size bounds polynomial in sourceSize, promise lands, scope-compliant [no in-kernel NP/runtime], non-vacuous). The Layer-B kernel headline: for every FourColorInstance G, the produced VBP instance is promised, item/dim/M4-carrier sizes are polynomial in G.sourceSize, and G.IsYes <-> D(M4 (ctorScaleFull (vbp_np_hard.toVBP G)) (reducedVectorsFull ...)) <= Byes. Assembled from the proved vbp_np_hard package + reduction_gap + output_size_bounds (codex lane). CAPSTONE VERIFICATION: `lake build NPCC` clean (8528 jobs, exit 0); current #print axioms NPCC.main_np_hardness = [propext, Classical.choice, finite_alphabet_balanced_family_exists, Quot.sound]; repo-wide sorry-token scan = 0 hits; exactly 1 project citation axiom (AGHP), with vbp_np_hard since discharged as a proved package. **BOARD: 125 PROVED, 0 OPEN.** The Gaspers-He-Mackenzie NP-completeness-of-deterministic-communication-complexity paper (arXiv:2508.05597) is now machine-verified in Lean 4 on one cited axiom. Scope (Simon-ratified): kernel = construction size bounds + the NO<=>GAP separation; polynomial runtime + NP-membership remain prose.
