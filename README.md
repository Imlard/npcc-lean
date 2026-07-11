# Lean-checked communication-complexity gap construction

This repository accompanies *NP-Completeness of Deterministic Communication
Complexity via Relaxed Interlacing* (Gaspers, He, Mackenzie;
[arXiv:2508.05597](https://arxiv.org/abs/2508.05597)). It contains a Lean 4
formalization of the paper's combinatorial gap construction and an interactive
paper-to-Lean explorer.

## Exact checked result

For every loopless edge-list instance `G` of 4-Colouring, Lean selects a typed
Boolean matrix `gapMatrix G`, pads it to a square power-of-two truth table
`gapTruthTable G`, and proves

```text
G is 4-colourable  <->  D(gapTruthTable G) <= gapBudget G
not 4-colourable  <->  gapBudget G + 1 <= D(gapTruthTable G).
```

The second line is the one-more-bit form of the same threshold equivalence. It
does **not** claim that the NO-instance cost is always exactly one bit larger.
Lean also proves `D(gapTruthTable G) = D(gapMatrix G)`: padding only
duplicates existing rows and columns. The short public statements are in
`lean/NPCC/Public.lean`.

The development also proves the source preprocessing specification, explicit
row/column carrier bounds, one fixed-degree polynomial dominating both
carriers in `|V|+|E|+1`, and a fixed-degree bound on the final truth-table bit
count. It builds with zero
`sorry` declarations. The transitive project-specific assumption is exactly
`NPCC.finite_alphabet_balanced_family_exists`, in addition to Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`.

## Formal boundary

The checked theorem is **not yet a formal polynomial-time many-one reduction**.
The following remain outside Lean:

- serialized bit-level source and target languages, including the formal
  relation between their encoding lengths and the checked combinatorial size;
- an executable balanced-family generator and its running-time proof;
- membership of the target decision problem in NP;
- the standard NP-hardness of 4-Colouring.

The matrix construction is noncomputable because it chooses balanced families
from the cited existence axiom. AGHP supplies the historical binary
almost-independence construction. The exact arbitrary-alphabet, relative-error
interface is sourced through Bshouty's derandomized Chernoff sampler and its
arbitrary-alphabet extension; the cylinder-event parameter translation is
recorded in
[`BALANCED-FAMILY-CITATION.md`](lean/docs/BALANCED-FAMILY-CITATION.md).

See [`lean/AUDIT.md`](lean/AUDIT.md) for the full trust report and
[`lean/PAPER-FINDINGS.md`](lean/PAPER-FINDINGS.md) for paper-to-Lean differences.
The shorter [`reviewer guide`](lean/docs/REVIEWER-GUIDE.md) gives a one-hour
route through the checked theorem and its external boundary.

## Live explorer

- [Term inspector](https://simonwmackenzie.github.io/npcc-lean/inspector/)
- [Dependency graph and PDF tracer](https://simonwmackenzie.github.io/npcc-lean/)

Both views link paper statements, Lean statements, and dependencies in both
directions. The downloadable Lean project is also available as
`npcc-lean-formalization.zip`.

## Repository layout

- `lean/NPCC/` - the paper-facing construction and proof.
- `lean/NPCC/Public.lean` - concise public theorem surface.
- `lean/NPCC/Padding.lean` - square power-of-two padding and exact `D`
  preservation.
- `lean/Workspace/` - reused, sorry-free communication-complexity library.
- `lean/claims/` and `lean/obligations.json` - statement ledger.
- `lean/pipeline/verify.mjs` - release-integrity checks.
- `lean/pipeline/package-release.py` - reproducible release bundle and checksum.
- `index.html`, `inspector/index.html`, `pages/`, `paper.pdf` - explorer site.

The explorer maps 62 of the paper's 65 numbered statements. The three omitted
statements (Corollary 17, Lemma 35, and Corollary 36 in arXiv v4) are not merely
cosmetic variants: as printed, they inherit a missing low-complexity guard. They
are not used by the final checked chain; see `lean/PAPER-FINDINGS.md`.

## Reproduce

Lean 4.30.0 is pinned by `lean/lean-toolchain`.

```sh
cd lean
lake exe cache get
lake build NPCC Workspace Tests
node pipeline/verify.mjs --lean
```

Release bundles are rebuilt with `python pipeline/package-release.py`; the
verifier checks the ZIP, both embedded downloads, and its SHA-256 checksum.

GitHub Actions runs the same checks on both Linux and Windows.

Citation metadata is in `CITATION.cff`. A repository license has not yet been
selected; that decision must be made before asking others to redistribute or
build derivative artifacts.
