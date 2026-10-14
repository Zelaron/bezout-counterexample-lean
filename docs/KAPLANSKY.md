# The gcd formulation of Kaplansky's condition

Copyright (c) 2026 Christian Hägg and Anders Mörtberg.

For the same constructed Bézout domain `BezoutCounterexample.R`, Lean proves

```text
∃ a b c, gcd a (gcd b c) = 1 ∧
  ∀ p q, gcd (p*a) (p*b + q*c) ≠ 1.
```

This is `BezoutCounterexample.exists_gcd_counterexample`. The unconditional
`BezoutCounterexample.main_theorem_gcd` packages the ring, commutative-ring and
normalized-gcd structures, domain and Bézout proofs, the first-order Bézout
identity, and this failed triple in one existential theorem. No construction or
gcd-existence hypothesis remains to be supplied by the user.

`KaplanskyConditionGCD` uses exactly

```text
∀ a b c, gcd a (gcd b c) = 1 →
  ∃ p q, gcd (p*a) (p*b + q*c) = 1.
```

The nesting of the triple gcd follows [Mörtberg's Coq formalization](https://staff.math.su.se/anders.mortberg/thesis/doc/theory/kaplansky.html).
Mathlib's `NormalizedGCDMonoid` supplies the ordinary gcd divisibility axioms
and normalization. Its structure on the counterexample is obtained from the
proved Bézout-domain instances using Mathlib's existence theorem and classical
choice. It is not an extra axiom. `BezoutCounterexample.gcd_eq_sum` proves
`∀ a b, ∃ x y, x*a + y*b = gcd a b` for this same structure.

The generic theorem `KaplanskyCondition.isBezout_iff_gcd_eq_sum` proves that this
first-order Bézout identity is equivalent to Mathlib's `IsBezout` property in a
domain with a genuine gcd structure. The coefficients multiply the original
arguments; `a*b + x*y = gcd a b` would not express the Bézout property.

`kaplanskyCondition_iff_gcd` proves equivalence with the existing unit-ideal
condition over every Bézout domain with a normalized gcd. Its two bridges prove
that the triple gcd generates exactly `(a,b,c)`, and that a normalized gcd is
one exactly when it is a unit; Mathlib's Bézout lemma identifies unit gcds with
linear-combination coprimality. The original bilinear obstruction therefore
proves failure of the gcd condition for the original constructed ring.

For an arbitrary choice of gcd, the invariant statement uses association to one
(multiplication by a unit), as does CoqEAL's `%= 1` notation.
`kaplanskyCondition_iff_gcdUpToUnits` proves that version equivalent to the
unit-ideal condition for any `GCDMonoid` structure, and
`kaplanskyConditionGCD_iff_upToUnits` connects it to literal equality after
normalization. This prevents the choice of gcd representatives from changing
what has been disproved.

The full elementary-divisor-domain characterization is not needed here. The
proved implication from the elementary-divisor property to Kaplansky's condition,
together with failure of the latter, gives the counterexample.

The compile, axiom-audit and kernel-replay checks described in the README include
these definitions and proofs. The original article and its numbered-statement map remain unchanged in this
local branch. The new declarations are included in the source compilation,
exhaustive axiom audit and kernel replay.
