# Source provenance and review

This project adapts selected proofs from the authors’ older formalization, `old/BezoutCounterexample-old`. The old source headers, theorem hypotheses and conclusions, mathematical definitions, and proof routes were compared with the shorter paper before reuse. All included project sources were compiled afresh in this project against pinned Mathlib dependencies.

The initial selection contained 40 source modules. Reuse is at the proof level: no compiled declarations from the old project are imported.

The substantive adaptations are:

- The main theorem is the existential Bézout/non-elementary-divisor result in the shorter paper.
- The key obstruction involves exactly five elements and equality to `1`.
- Proposition 5.2 states the Bézout-domain conclusion; the old strengthened statement and the old final section are omitted.
- Proposition 4.6 has an explicit two-element statement. The more general ideal version is retained as an auxiliary theorem used in its proof.
- `Principalization/CompactLift.lean` extracts only the needed compact-lift fact from the old `Strong.lean`; the old strengthened principalization result is omitted.
- `AssociatedGraded.lean` adds the ring structure, ring isomorphism, homogeneous multiplication, and domain result needed for Lemma 3.5(5).
- Theorem 3.3(2) formalizes the polynomial-localization case needed by the construction; Theorem 3.6 follows the affine vertex and scaling proof. Their scope is described in [STATEMENTS.md](STATEMENTS.md).

The old explicit/countable quotient construction files are not part of this project. Useful intermediate algebraic results remain where they support the included proofs.

This source distribution contains no caches or build artifacts. A fresh checkout obtains the pinned third-party dependencies from `lake-manifest.json` with `lake exe cache get`. The article is distributed separately and is not needed to compile or verify the formalization.
