# Paper-to-Lean findings

Canonical comparison against arXiv:2508.05597 v4. These are manuscript issues,
not failures of the final checked Lean theorem: the Lean statements include the
needed guards, and the final use sites satisfy them.

## F1 - Lemma 12 needs `H > 1`

**Status:** statement false as printed; guarded repair proved in Lean.

Lemma 12 allows arbitrary real `H`. The finite example

```text
M = [0 1],  x = 1/2,  y = 3/5,  H = 1
```

satisfies the three one-copy hypotheses. The two-copy middle conclusion fails
because its column threshold is one, so a monochromatic one-column restriction
has complexity zero rather than at least one. The top conclusion also fails:
the two diagonal columns give two identical rows and communication complexity
one rather than two.

Lean's `NPCC.two_copy_ladder` adds `1 < H`; that repaired theorem is proved.

Consequences for the manuscript:

- Corollaries 15 and 16 need `D(M) >= 2`.
- Corollary 17 inherits the same requirement.
- Lemma 35 needs `H > 1`.
- Corollary 36 cannot apply the repaired Lemma 35 for the full printed range
  `0 <= k <= D(M)`, because `H = D(M)-k` can be zero or one. Restrict the range
  to `D(M)-k > 1`, prove the endpoint cases separately, or remove the corollary
  if it is unused.

Corollary 17, Lemma 35, and Corollary 36 are the three numbered paper statements
not represented as nodes in the formalization. They should not be described as
harmless exposition variants until their guards are repaired.

## F2 - Lemma 33 has a quantifier-order mismatch

**Status:** intended nonuniform version proved; stronger uniform version not
established by this artifact.

The printed wording fixes `j` and then says "for all sufficiently large powers
of two `t`" before quantifying over robust matrices. Read literally, the
threshold is uniform in the robustness margin `delta`. Lean proves the version
where `j` and `0 < delta < 1/2` are fixed before choosing the threshold:

```text
forall j delta, exists m0 = m0(j, delta), ...
```

This matches the final reduction, where `delta` is a fixed construction
constant. Quantitative analysis indicates that a threshold uniform as
`delta -> 1/2` is problematic, but this release proves neither that stronger
statement nor its negation. The manuscript should state explicitly that the
threshold may depend on `delta`.

## F3 - Lemma 25 needs `D(M) >= 2`

**Status:** statement false as printed; strengthened Lean statement proved.

Lean's `failure_to_separate_gives_gap` includes `2 <= D f`, absent from paper
Lemma 25. The guard is load-bearing. A direct finite counterexample is:

```text
M: 8 x 2 with M(row, col) = col
delta = 1/10, b = 5, q = 2, x = 1
y = (1/2 + delta)^2 = 9/25.
```

Then `M` is robust and `D(M)=1`. In the two-copy interlace, keep all rows and
the two diagonal columns. The resulting bracket member has communication
complexity one. A constant one-bit Alice query has a single nonempty part, so
the near-exact no-waste conclusion fails, but no child can have complexity
`D(M)+1=2`. The threshold inequality is `q*T = 2 < 8 = T0`.

Add `D(M) >= 2` to Lemma 25. The classical and relaxed separation theorems
already assume this, so the final checked reduction is unaffected.

## F4 - "Every branch" must mean a surviving branch

**Status:** clarification required.

The paper's separation language says the first bits have the prescribed speaker
on every branch. Lean's `FirstKRowBitsOn` and `FirstKColBitsOn` impose that
condition only while the current rectangle is nonempty. An arbitrary protocol
tree may contain dead subtrees with no realizing input, where the next node can
be a leaf or the other speaker without affecting computation.

Replace "every branch" by "every surviving/input-realizable branch," or define
protocols with dead subtrees pruned.

## F5 - The AGHP citation does not state the exact Lean interface verbatim

**Status:** citation/derivation gap at the sole project axiom.

The Lean axiom supplies an arbitrary finite alphabet, relative pointwise error
on every projection of size at most `t`, and one explicit size bound. The cited
AGHP result is presented for binary variables. The manuscript should derive the
needed finite-alphabet form, including the error rescaling and size accounting,
or cite a theorem that states it directly. Deterministic constructibility is
also not included in the Lean axiom.

## Final-chain impact

The audited `reduction_gap` and `main_np_hardness` use the guarded Lean lemmas
and discharge their guards. No defect from F1-F4 was found in the final Lean
equivalence. F5 remains the explicit external axiom boundary.
