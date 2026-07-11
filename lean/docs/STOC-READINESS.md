# Simplification and STOC-readiness strategy

This document is a review strategy, not a prediction of acceptance. Correctness
is necessary but not sufficient; novelty, conceptual compression, comparison
with concurrent work, and presentation to a broad theory audience will decide
the outcome.

The latest official STOC call available during this audit (STOC 2026) says the
initial twelve pages should explain the work's merits, importance, and key
conceptual ideas to a broad TCS audience, while the submitted proof material
must permit full verification:

https://acm-stoc.org/stoc2026/stoc2026-cfp.html

## Recommended six-step proof spine

1. **Classical amplification.** State one theorem saying what hardness survives
   after interlacing; move the rung recurrences to an appendix.
2. **Hard seed.** Make `hard_seed` the sole paper-facing output of the classical
   engine and fix the `delta` quantifier before the threshold.
3. **Balanced-family transfer.** Introduce one precise transfer certificate:
   balanced projections recover a classical hard subgame with a controlled
   density loss.
4. **Protocol rigidity.** Present Extension and Separation as two consequences:
   a tight protocol must spend its early bits identifying outer blocks.
5. **Scaffold certification.** Collapse Stages 1-4 into one theorem saying the
   scaffold has a cheap YES protocol and any cheap protocol induces a valid
   four-bin partition.
6. **Concrete reduction and amplification.** Give the 4-Colouring
   preprocessing, the one-bit gap, square truth-table representation, explicit
   size/runtime accounting, and then the ETH gap-amplification step.

The first twelve pages should reach steps 3-4 quickly. At present, too much of
the conceptual novelty is hidden behind classical interlace mechanics before
the reader sees the relaxed transfer and rigidity ideas.

## Position against the concurrent result

Hirahara, Ilango, and Loff posted *Communication Complexity is NP-hard*
(arXiv:2507.10426) on 14 July 2025. The present paper was first posted on
7 August 2025. Because target NP membership is comparatively standard, the
headline NP-hardness/NP-completeness result alone is unlikely to distinguish a
STOC submission from that concurrent route.

The planned ETH-based inapproximability extension changes this comparison. If
completed with explicit factors and running-time exponents, it is strictly
stronger than exact NP-hardness and should be the lead theorem. The exact
NP-hardness result then serves as the audited base case rather than the sole
novelty claim. Until that extension is proved, the submission should not rely
on it rhetorically.

The paper should make a theorem-level case for relaxed interlacing in either
version:

1. State Extension and Separation as reusable results before specializing any
   scaffold parameters.
2. Explain the obstacle they solve: full Cartesian column products preserve
   hardness but are exponentially large; almost-independent columns preserve
   both hardness and the shape of every tight protocol.
3. Compare proof length, quantitative loss, and generality directly with the
   concurrent construction.
4. Use the ETH inapproximability theorem as the concrete second payoff: isolate
   the amplification theorem and show exactly where rigidity makes it possible.

The formal artifact is strong supporting evidence, but it cannot substitute
for this novelty argument.

## Suggested first-twelve-page budget

1. **Pages 1-2:** ETH inapproximability theorem, exact base case,
   simultaneous-work comparison, and precise contribution.
2. **Pages 3-4:** the exponential-column obstacle and relaxed-interlace idea.
3. **Pages 5-7:** relaxed-to-classical bridge, Extension, and Separation.
4. **Pages 8-10:** one scaffold-certification theorem and its proof sketch.
5. **Pages 11-12:** concrete one-bit reduction, amplification to the ETH gap,
   size/runtime accounting, and a precise roadmap to the appendices.

The page boundary should not cut between the gap theorem and its size/runtime
closure; otherwise a broad reviewer can reasonably leave the core claim
unverified.

## Remove or demote

- Delete unused Corollary 17, Lemma 35, and Corollary 36 after checking no later
  prose refers to them.
- Move most ceiling arithmetic, parameter feasibility, and rung-by-rung density
  calculations to appendices.
- Keep one running diagram of the matrices `M0 -> M1 -> M2 -> M3 -> M4`; do not
  introduce each stage as an independent conceptual object when it is only a
  certified adapter.
- Promote the generic no-waste/stopping-time principle and make the stage
  theorems short instantiations.
- Avoid production vocabulary such as "tranche," "binding ruling," "ratified,"
  or model-session provenance in mathematical exposition.

## Close the formal boundary

The highest-value additions to Lean are not more internal stage lemmas. The
remaining bridge results reviewers will ask for immediately are:

1. an executable implementation of the now precisely sourced finite-alphabet
   balanced-family theorem;
2. serialized source and target languages, together with a proof that their
   encoding lengths are polynomially related to the checked combinatorial size
   `|V|+|E|+1`; the fixed-exponent carrier and padded truth-table bounds in
   that combinatorial size are now proved;
3. an explicit reduction function/specification/runtime theorem;
4. a small public theorem for the ETH amplification and its quantitative size
   recurrence.

Square power-of-two padding and preservation of `D` are now proved in
`NPCC.Padding` and exposed for the final reduction in `NPCC.Public`.

Only after those are present should the artifact headline say "Lean-verified
NP-hardness reduction." Target NP membership can remain a short independent
wrapper if it is genuinely standard and precisely stated.

## Reviewer-facing Lean API

Keep the public surface to roughly a dozen declarations:

- source instance and YES predicate;
- `sourceVBP`, promise, and source YES equivalence;
- balanced-family certificate and its exact assumption;
- one relaxed-transfer theorem;
- one scaffold certificate;
- `gapMatrix`, `gapBudget`;
- YES iff budget;
- NO iff one-more-bit;
- fixed-degree carrier and truth-table size theorem;
- executable reduction and runtime theorem (still external);
- final padded Boolean-function theorem.

`NPCC/Public.lean` is the first step. Internal stage interfaces can remain in the
artifact without being part of the recommended reader journey.

## Social validation plan

1. Publish a corrected anonymous manuscript and a tagged artifact commit.
2. Make Linux and Windows CI mandatory and expose exact axiom/sorry checks.
3. Archive the release with a DOI and record checksums for the PDF and Lean zip.
4. Supply a one-page trust map: theorem, assumptions, unformalized wrapper, and
   exact reproduction commands.
5. Ask at least two communication-complexity experts and one Lean expert to
   review separate, explicit checklists; preserve their issues and resolutions.
6. Compare the route directly with concurrent work. Claim a reusable framework
   only if the paper demonstrates a second payoff or a concrete consequence not
   obtained more simply elsewhere.
7. Separate the minimal reviewer artifact from production logs and historical
   planning material; retain the latter in a provenance archive.

## Acceptance-risk summary

- **Blocking:** false/mismatched paper statements and any overbroad
  machine-verification headline. The balanced-family source chain is now
  explicit, although executable generation remains external.
- **Major:** the first-twelve-page story and the lack of a closed serialized,
  executable reduction wrapper. The internal fixed-degree size bound is now
  checked.
- **Strategic:** complete the ETH inapproximability extension and demonstrate
  that relaxed interlacing/rigidity is what enables the stronger result.
- **Artifact:** portable CI, minimal public API, upstream reuse provenance,
  an author-approved license, and a reproducible site generator. Citation
  metadata is now present; the license decision remains open.
