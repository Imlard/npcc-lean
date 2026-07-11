# Build and verification guide

The project pins Lean 4.30.0 in `lean-toolchain` and Mathlib `v4.30.0` in
`lakefile.toml`.

## Reproduce the release check

```sh
lake exe cache get
lake build NPCC Workspace Tests
node pipeline/verify.mjs --lean
```

`NPCC` is the formalization, `Workspace` is the reused library, and `Tests` is
an isolated regression-test library. Building all three prevents an unimported
source file from escaping CI. GitHub Actions repeats the build on Linux and
Windows and also runs Lean's standalone environment checker.

The verifier checks:

- all 126 ledger obligations are closed as `proved`;
- every registered claim block still matches its Lean source;
- there are no executable `sorry`, `admit`, or source `unsafe` declarations;
- the only direct project axiom is `finite_alphabet_balanced_family_exists`;
- `NPCC.lean` and `Workspace.lean` cover their source modules;
- the two explorers contain identical graph data;
- every embedded graph statement is an exact substring of its Lean source;
- the headline theorem has exactly the documented transitive axiom footprint;
- the downloadable ZIP contains exact copies of every non-build Lean source
  file plus citation metadata, both explorers embed those same bytes, and the
  SHA-256 checksum is current.

## Regenerate the release archive

After changing any file under `lean/`, run:

```sh
python pipeline/package-release.py
```

This deterministically rebuilds `npcc-lean-formalization.zip`, updates the
embedded download in both explorers, and writes
`npcc-lean-formalization.zip.sha256`. The verifier checks all three copies.

## Direct axiom reports

```sh
lake env lean AxiomReport.lean
lake env lean wrapper_check.lean
```

Expected footprint for `NPCC.main_np_hardness` and the public gap theorems:

```text
propext
Classical.choice
NPCC.finite_alphabet_balanced_family_exists
Quot.sound
```

The source 4-Colouring-to-VBP package `NPCC.vbp_np_hard` uses only `propext`,
`Classical.choice`, and `Quot.sound`, without the project citation axiom.

## What a successful build certifies

A successful check certifies a choice-based matrix construction with the exact
4-Colouring/communication-budget equivalence, explicit carrier bounds,
fixed-degree domination in `|V|+|E|+1`, square power-of-two truth-table
padding, a polynomial truth-table bit count, and exact preservation of `D`.
It does not certify the remaining external complexity-theory wrapper:
serialized languages and their encoding-length bridge, executable construction
and runtime, target NP membership, or the known NP-hardness of 4-Colouring.
See `AUDIT.md` and `docs/BALANCED-FAMILY-CITATION.md`.
