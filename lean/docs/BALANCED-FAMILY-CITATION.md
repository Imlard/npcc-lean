# Balanced-family citation boundary

## Purpose

The reduction uses an indexed multiset of words `S : Fin L -> Fin q -> Y`
over an arbitrary nonempty finite alphabet `Y`. For every coordinate set
`J` of size at most `t` and every pattern on `J`, its empirical frequency must
be within relative error `epsilon` of the uniform probability
`|Y|^(-|J|)`. The Lean assumption is
`NPCC.finite_alphabet_balanced_family_exists`.

This is not a verbatim theorem from Alon--Goldreich--Hastad--Peralta (AGHP).
AGHP's Theorem 2 constructs binary almost-wise-independent sample spaces in
max norm. The finite-alphabet statement used by this project is more directly
obtained from the derandomized Chernoff-with-union-bound theorem of Bshouty.

Primary sources:

- N. Alon, O. Goldreich, J. Hastad, R. Peralta, *Simple Constructions of
  Almost k-wise Independent Random Variables* (1992), especially Definition 2
  and Theorem 2: https://www.wisdom.weizmann.ac.il/~oded/PSX/aghp.pdf
- N. H. Bshouty, *Derandomizing Chernoff Bound with Union Bound with an
  Application to k-wise Independent Sets*, ECCC TR16-083 (2016), especially
  Corollary 3 and the stated arbitrary-alphabet/product-distribution extension:
  https://eccc.weizmann.ac.il/report/2016/083/

## Parameter translation

Let `m = |Y|` and take the ambient probability space to be the uniform
distribution on `Y^q`. For every `J subseteq [q]`, `|J| <= t`, and every
pattern `a : J -> Y`, introduce the indicator

```text
X_(J,a)(s) = 1  iff  s restricted to J equals a.
```

Its expectation is exactly `p_(J,a) = m^(-|J|)`. Apply Bshouty's relative
sampler with tolerance `epsilon` simultaneously to all these indicators. The
output is a multiset of ambient words; enumerate its occurrences by `Fin L`.
The two relative inequalities are exactly

```text
| empirical_frequency(J,a) - m^(-|J|) |
  <= epsilon * m^(-|J|),
```

which is `IsBalancedFamily`.

There are at most `2^q * m^t` relevant cylinder events and the smallest event
probability is at least `m^(-t)`. Corollary 3 therefore gives a sample size
bounded by

```text
O((q + t log m) * m^t * epsilon^(-2)).
```

After increasing one universal positive constant, this is bounded by the
deliberately loose expression used in Lean:

```text
(q + 2)^C * (m + 2)^(C*t) * ceil(1/epsilon)^C.
```

This explains every quantifier and factor in the citation interface. In
particular, multiplicity is intentional: Bshouty's output is a multiset, and
Lean samples uniformly from its indices rather than deduplicating equal words.

## What remains external

Lean assumes the displayed finite-alphabet existence-and-size corollary. It
does not formalize Bshouty's potential-function construction or its bit-time
analysis. Consequently the selected family is noncomputable in the current
development. This boundary is sufficient for the kernel-checked correctness
and carrier-size theorems, but an executable polynomial-time reduction still
requires an implemented generator and an encoded runtime analysis.
