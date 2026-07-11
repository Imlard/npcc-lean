# NPCC Lean formalization

This directory is the reproducible Lean 4 project for the communication-
complexity gap construction accompanying arXiv:2508.05597.

## Start here

1. Read `NPCC/Public.lean` for the exact public theorem.
2. Read `AUDIT.md` for what was checked and what remains external.
3. Read `PAPER-FINDINGS.md` before comparing the Lean statements with arXiv v4.
4. Use `docs/REVIEWER-GUIDE.md` for a short review route.
5. Use `BUILD.md` to reproduce the kernel and integrity checks.

The key public equivalences are:

```text
NPCC.fourColorable_iff_gapTruthTable_cost_le
NPCC.not_fourColorable_iff_gapTruthTable_cost_at_least_one_more
```

They say that 4-colourability is equivalent to meeting the communication budget,
and non-colourability is equivalent to needing at least one additional bit.
`NPCC.gapTruthTable_cost` proves that the square power-of-two padding preserves
the complexity of the internal typed matrix exactly.

## Trust boundary

The Lean kernel checks the selected matrix's gap theorem, explicit carrier
bounds, fixed-degree domination in the combinatorial source size, square
power-of-two padding, its polynomial bit count, and exact preservation of `D`. The only
project axiom in the transitive footprint is
`NPCC.finite_alphabet_balanced_family_exists`; the construction is
noncomputable because it uses that existence theorem by choice. The precise
AGHP/Bshouty citation chain and parameter translation are in
`docs/BALANCED-FAMILY-CITATION.md`.

Lean does not currently certify an executable polynomial-time reduction, a
serialized bit-level source/target language and encoding-length bridge, target
NP membership, or 4-Colouring's NP-hardness.

## Layout

- `NPCC/` - paper-facing definitions, transfers, stages, reduction, and wrapper.
- `NPCC/Public.lean` - concise theorem surface for reviewers.
- `NPCC/Padding.lean` - square truth-table padding and `D` preservation.
- `NPCC/PolynomialSize.lean` - fixed-degree domination of the size expressions.
- `Workspace/` - reused communication-complexity library.
- `Tests/` - isolated regression tests not used by the main theorem.
- `claims/`, `obligations.json` - frozen statement ledger and provenance.
- `pipeline/verify.mjs` - source, claim, axiom, and inspector integrity checks.
- `pipeline/package-release.py` - reproducible ZIP, checksum, and site embedding.
- `docs/` - current manuscript notes plus clearly marked historical records.

`loop-log.md`, `RECAP-2026-07-06.md`, and the files listed as historical in
`docs/README.md` are provenance records, not current correctness claims.

## Build

```sh
lake exe cache get
lake build NPCC Workspace Tests
node pipeline/verify.mjs --lean
```

For a release, regenerate the public download after all source changes, then
rerun the verifier:

```sh
python pipeline/package-release.py
node pipeline/verify.mjs --lean
```

The module and directory names intentionally use the same `NPCC` casing so the
project builds on case-sensitive filesystems as well as Windows.
