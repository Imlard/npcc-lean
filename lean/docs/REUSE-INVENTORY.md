# Reused Workspace layer

`Workspace.lean` imports all 33 production modules under `Workspace/`. The
former unimported `Workspace/DigitTest.lean` has been moved to the isolated
`Tests` library and renamed so it no longer collides with production
declarations.

## Re-verification

The production layer is built by:

```sh
lake build Workspace
lake env lean AxiomReport.lean
```

Under Lean 4.30.0 and Mathlib v4.30.0, the four reported Workspace headline
theorems depend only on:

```text
propext
Classical.choice
Quot.sound
```

They do not depend on the project balanced-family citation axiom.

## Provenance qualification

The repository contains the complete source snapshot used by this proof, so it
is kernel-auditable and reproducible. It does not currently contain a verifiable
upstream repository URL plus commit hash, license, or a mechanically checked
proof that this snapshot is byte-identical to an upstream Mackenzie-Saffidine
release. Add those items before describing the layer as an unchanged upstream
artifact.
