# Formalization audit

Audit date: 2026-07-11  
Baseline audited: commit `76320b8`  
Candidate audited: the current local release tree (not yet published)  
Scope: Lean source, paper-to-Lean translation, build/axiom footprint, claim
ledger, downloadable archive, and both interactive explorers.

## Verdict

The central Lean result is real and bidirectional. Assuming the single
balanced-family axiom, the development proves that the matrix selected from a
loopless edge-list 4-Colouring instance meets the YES communication budget if
and only if the graph is 4-colourable. Because the costs are natural numbers,
the negation is equivalent to requiring at least one more bit.

No vacuous implication, reversed direction, or off-by-one error was found in
the final gap chain. The preprocessing promise and YES-equivalence are proved,
and the soundness direction uses the NO lower bound rather than assuming the
desired converse.

The artifact does **not** yet prove full NP-hardness as a formal complexity-
theory theorem. Its public language must keep the following distinction clear:

- **kernel-checked:** the selected typed matrix, gap equivalence, preprocessing,
  protocol lower/upper bounds, explicit carrier formulas, fixed-degree
  domination in `|V|+|E|+1`, and final square power-of-two padding with a
  polynomial bit count and exact preservation of `D`;
- **external:** serialized source/target languages and their encoding-length
  bridge, executable construction and runtime, NP membership, and the source
  problem's known NP-hardness.

## Exact public theorem

`NPCC/Public.lean` defines `gapMatrix G`, its conventional square padding
`gapTruthTable G`, and `gapBudget G`. It proves:

```text
NPCC.gapTruthTable_cost:
  D (gapTruthTable G) = D (gapMatrix G)

NPCC.fourColorable_iff_gapTruthTable_cost_le:
  G.IsYes <-> D (gapTruthTable G) <= gapBudget G

NPCC.not_fourColorable_iff_gapTruthTable_cost_at_least_one_more:
  (Not G.IsYes) <-> gapBudget G + 1 <= D (gapTruthTable G)
```

The second statement is a threshold lower bound. It does not say that every NO
instance has cost exactly `gapBudget G + 1`.

The underlying generic theorem is `NPCC.reduction_gap` in `NPCC/Gap.lean`:

```text
I.IsYes    -> D(M4(I)) <= Byes
not I.IsYes -> Byes < D(M4(I)).
```

`NPCC.main_np_hardness` in `NPCC/Wrapper.lean` composes this with the proved
4-Colouring-to-VBP map.

## Translation audit

| Paper role | Lean declaration | Audit result |
| --- | --- | --- |
| Source reduction, Proposition 42 | `toVBP_yes_iff`, `toVBP_promise` | Exact for loopless edge-list graphs. Indexed vertices preserve multiplicity. |
| Zero-anchor preprocessing | `zero_anchor_preprocessing` and companions | YES iff preserved; canonical anchors and the NO overloaded-coordinate witness are both proved. |
| YES protocol | `scaffold_completeness` | Produces cost at most `Byes`; no hidden NO assumption found. |
| NO protocol lower bound | `reduction_gap` via `M4_no_waste_lift` and `local_kill` | Strict lower bound proved; all large-parameter and protocol-control gates are discharged by constructor certificates. |
| Gap wrapper | `main_np_hardness` | Contains the literal `G.IsYes <-> D(M4) <= Byes` final conjunct. |
| Relaxed-to-classical bridge | `relaxed_to_classical` | Row trimming, projected-pattern multiplicity, column-density loss, and value-level reindexing agree with the paper. |
| Extension theorem | `extension_theorem` | Cost ledger, seed threshold, bridge density, and terminal alternatives agree with the paper. |
| Separation theorem | `relaxed_separation` | Correct for surviving/nonempty branches; see the branch-language qualification below. |
| Output size | `output_size_bounds`, `main_output_size_fixed_degree`, `gapTruthTableBitCount_le_fixed_polynomial` | Proves the exact formulas, one fixed-degree carrier polynomial in `|V|+|E|+1`, and a fixed-degree bound on the square truth-table bit count. |
| Square truth-table padding | `gapTruthTable_cost`, `gapTruthTableSize_eq_two_pow` | Produces equal power-of-two input domains and preserves `D` exactly by surjective duplicate padding. |

## High-priority qualifications

### 1. Effective NP-hardness is not formalized

The selected balanced families, global threshold, normalized vectors, and final
matrix are noncomputable choices. There is no encoded-language definition,
Turing-machine reduction, running-time proof, or target NP-membership theorem.
The theorem name `main_np_hardness` is historical; its type is the authority.

### 2. Fixed-degree size is checked; serialized encodings remain external

Lean now proves the previously missing statement

```text
rowPoly d <= d^K and colPoly d <= d^K
```

on the normalized constructor regime, for the absolute exponent
`fixedStructuralDegree`. `main_output_size_fixed_degree` bounds both carriers
by `sourceCarrierPolynomial (|V|+|E|+1)`, and
`gapTruthTableBitCount_le_fixed_polynomial` includes the square padding.

What remains external is the definition of serialized source and target
languages and the proof relating their bit lengths to this combinatorial size.
`sourceSize = |V| + |E| + 1` is still a combinatorial proxy, not itself a
formal string length.

### 3. The balanced-family theorem remains the sole citation axiom

`finite_alphabet_balanced_family_exists` is the exact arbitrary-finite-alphabet,
relative-pointwise-error, size-bounded interface used by the proof. AGHP is
phrased for binary random variables and is not presented as a verbatim source
for this stronger statement. `docs/BALANCED-FAMILY-CITATION.md` now gives the
precise source chain through Bshouty's derandomized Chernoff sampler, its
arbitrary-alphabet extension, and the cylinder-event parameter translation.

The axiom also omits deterministic constructibility, so it cannot support the
runtime claim by itself.

### 4. Several paper statements require repairs already present in Lean

The final Lean chain is protected, but arXiv v4 contains missing low-complexity
guards and one quantifier-order mismatch. The canonical list and concrete
counterexamples are in `PAPER-FINDINGS.md`. In particular, Lemma 12 and its
descendants cannot be advertised as literally formalized without mentioning
the added guard.

### 5. "Every branch" means every surviving branch

Lean's protocol-control predicates permit an early leaf or the wrong speaker on
an empty rectangle. Thus the checked theorem controls every branch realized by
some input in the current rectangle, which is the operational notion used by
the proof. The manuscript should say "every surviving (input-realizable)
branch" or explicitly prune dead subtrees.

## Mechanical verification

The following checks were reproduced locally:

```sh
lake build NPCC Workspace Tests
lake env lean AxiomReport.lean
lake env lean wrapper_check.lean
node pipeline/verify.mjs --lean
```

### Explorer explanation audit

The baseline explorer's 137 nodes and 807 Lean-block explanations received a
separate statement-by-statement audit. It identified 114 explanation entries
across 36 nodes requiring at least one change: 103 source-line re-anchors, 14
concept corrections, and one label correction. The correction set is recorded
in `pipeline/explainer-audit.json` rather than only in generated HTML.

During integration into this 139-node candidate, all 14 conceptual corrections
and the label correction were checked against the current embedded Lean
statements. One correction was strengthened: the amplification tooltip now
records the missing `2^k` factor while also describing `LambdaGE` correctly as
a communication-complexity lower bound, not as a density measure. The two new
candidate-only nodes retain their separately authored explanations.

`pipeline/sync-inspector.mjs` resolves every audited line anchor against the
current Lean statement and fails if an anchor disappears. The integrity
verifier checks the correction count, changed-node count, exact concepts and
labels, and all 103 resolved source lines, preventing a later rebuild from
silently discarding this audit.

Observed trust facts in the audited build:

- all 126 ledger obligations had status `proved`;
- all 68 local Lean modules were covered by the three Lake roots `NPCC`,
  `Workspace`, and `Tests`;
- the main theorem built with zero `sorry` declarations;
- the only direct project axiom declaration was
  `NPCC.finite_alphabet_balanced_family_exists`;
- `NPCC.main_np_hardness` depended on `propext`, `Classical.choice`,
  `NPCC.finite_alphabet_balanced_family_exists`, and `Quot.sound`;
- `NPCC.vbp_np_hard` depended only on the three standard Lean axioms;
- every one of the 139 graph `leanStmt` blocks was an exact normalized
  substring of its recorded source file;
- the two explorers contained identical graph data;
- the downloadable archive matched the non-build files in `lean/`, included
  citation metadata, and was byte-identical to both embedded site downloads.

The project-owned `NPCC` layer emits no Lean linter warnings in the audited
build. The reused `Workspace` snapshot still emits inherited deprecation,
namespace, and unused-proof warnings; these do not change theorem statements or
axiom footprints and were not silently suppressed or rewritten in this audit.

The audit also found and corrected release-engineering defects: module casing
that failed on Linux, a CI step that masked an axiom-report failure, a claim file
with an extra terminal CRLF, stale public URLs/scope text, an unimported scratch
module, a misleading comment that called a proved log-rank theorem an axiom,
and a stale downloadable ZIP. The release check now covers Linux and Windows,
the standalone Lean environment checker, exact claims and axiom footprints,
all explorer snippets, and the embedded archive checksum.

## Confidence

- **High confidence:** the formal theorem really proves the bidirectional
  threshold gap for both the selected typed matrix and its square power-of-two
  truth table, conditional on the balanced-family citation axiom.
- **High confidence:** the source preprocessing and the extension/separation
  chain used by the final theorem are nonvacuous and correctly connected.
- **High confidence:** the current Lean theorem is not an effective NP-hardness
  theorem and should not be described as one without the external wrapper.
- **High confidence:** the fixed-degree carrier and truth-table size bounds are
  kernel-checked; the variable Stage-2 exponent is discharged explicitly.
- **Medium confidence:** the executable balanced-family construction can be
  connected to the cited sampler with the intended polynomial runtime; that
  effective construction is not formalized in this audit.

## Recommended closure order

1. Correct the manuscript statements listed in `PAPER-FINDINGS.md`.
2. Define conventional serialized source/target languages and connect their
   bit lengths to the checked combinatorial size polynomial.
3. Replace noncomputable choice with an executable balanced-family generator
   and state an actual polynomial-time reduction theorem.
4. Add the standard NP-membership wrapper only after the checked reduction
   boundary is exact.
5. Record an upstream commit and license for the reused `Workspace` snapshot,
   and select an author-approved license for this repository.
