# Manuscript edits required by the Lean audit

This is the actionable edit list for arXiv:2508.05597 v4. The canonical
mathematical details and counterexamples are in `../PAPER-FINDINGS.md`.

## Must fix before expert circulation

### 1. Lemma 12: add `H > 1`

The printed statement is false at `H=1`. Lean proves the repaired theorem
`NPCC.two_copy_ladder` with `1 < H`.

### 2. Corollaries 15, 16, and 17: add `D(M) >= 2`

Each consumes the two-copy ladder with `H=D(M)`. Robustness alone gives only
`D(M) >= 1`.

### 3. Lemma 35 and Corollary 36: repair or delete

Lemma 35 inherits `H>1`. Corollary 36 invokes it with `H=D(M)-k` over a range
that includes `H=1` and `H=0`, so adding a hypothesis only to Lemma 35 is not
enough. These statements appear unused by the final proof; deletion is the
cleanest option unless a separate endpoint argument is useful.

### 4. Lemma 25: add `D(M) >= 2`

The paper proof invokes Corollary 16, whose repaired form needs this guard. Lean
already includes it in `NPCC.failure_to_separate_gives_gap`. The 8-by-2
counterexample is recorded in `../PAPER-FINDINGS.md`.

### 5. Lemma 33: make the threshold depend on `delta`

State that `j` and `0 < delta < 1/2` are fixed before "sufficiently large."
Lean proves a threshold `m0(j,delta)`, not a threshold uniform in `delta`.

### 6. Separation statements: say "surviving branch"

Replace "every branch" by "every input-realizable/surviving branch," or define
protocols after pruning dead subtrees. This is the exact semantics checked by
`FirstKRowBitsOn` and `FirstKColBitsOn`.

### 7. Balanced-family citation: use the exact source chain

Do not attribute the displayed arbitrary-alphabet statement verbatim to AGHP.
AGHP gives the historical binary construction. Cite Bshouty's derandomized
Chernoff sampler and explicit arbitrary-alphabet extension for the exact
finite-alphabet corollary, and include the cylinder-event parameter translation
from `docs/BALANCED-FAMILY-CITATION.md`. The Lean axiom covers existence and
size only; deterministic construction time must still be stated and justified
in the manuscript.

## Scope wording to use consistently

Until the missing complexity wrapper is formalized, describe the artifact as:

> Lean verifies the choice-based communication-gap construction and explicit
> fixed-degree carrier and truth-table bounds in the combinatorial source size,
> together with square power-of-two padding that preserves deterministic
> communication complexity, conditional on one balanced-family citation axiom.

Do not say that Lean proves a polynomial-time many-one reduction or the full
NP-completeness theorem. Serialized languages and their encoding-length
bridge, runtime, NP membership, and source NP-hardness remain external.

## STOC and ETH-inapproximability strategy

The planned ETH-based inapproximability extension should become the submission's
main theorem-level differentiator. If completed, it is strictly stronger than
the exact NP-hardness statement and materially reduces the concurrency risk.
Until the proof is complete, describe it as work in progress rather than as a
claimed contribution.

### The theorem ladder

1. State the present one-bit threshold gap as the base reduction theorem.
2. State a separate quantitative gap-composition or amplification theorem with
   every parameter visible.
3. Derive the ETH consequence as a clean corollary: specify the approximation
   factor, input size, and forbidden running time exactly.
4. Make explicit which parts reuse relaxed interlacing and protocol rigidity;
   this is the conceptual reason the stronger theorem is not merely a wrapper.
5. Keep the exact NP-hardness result independently checkable, so a reviewer can
   validate the base theorem even while reading the ETH extension.

### First twelve pages

- Pages 1-2: lead with the ETH inapproximability theorem, then identify exact
  NP-hardness as its base case; compare precisely with concurrent work.
- Pages 3-5: explain the exponential-column obstacle and the relaxed-interlace
  solution in ordinary communication-complexity language.
- Pages 6-8: present the transfer and rigidity theorems as the reusable engine.
- Pages 9-10: give one scaffold-certification theorem producing the one-bit gap.
- Pages 11-12: explain the gap amplification/ETH step and close the size and
  runtime accounting; send technical recurrence arithmetic to appendices.

### Artifact organization for the extension

- Keep `NPCC.Public` as the stable base-gap API.
- Put the ETH extension behind a separate small public module whose assumptions
  and quantitative conclusion are visible in one theorem.
- Add executable small-instance regression tests for every gap-amplification
  transformation before attempting the full asymptotic proof.
- Extend the trust map with a second path: base gap -> amplification -> ETH
  consequence, marking any external ETH theorem or encoding assumption exactly.
- Do not expand the current inspector into every internal amplification lemma;
  add only the public extension theorem and its five to ten conceptual steps.

## Optional simplifications

- Remove unused Corollary 17, Lemma 35, and Corollary 36 rather than maintaining
  a second low-level two-copy interface.
- Present `hard_seed` as the public output of the classical amplification
  section; move rung recurrences and most density arithmetic to an appendix.
- State once that balanced-family arguments always use `t <= q`.
- Note that Stage-1 thresholding is direct rectangle counting, not an
  application of robustness.
- Explain that the enormous `d_star` is an explicit absolute constant absorbed
  by per-instance padding; do not make readers infer this from the arithmetic.
- Factor Extension and Separation through one named transfer certificate so
  their shared hypotheses are introduced only once.
