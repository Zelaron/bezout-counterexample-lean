# A Bézout domain that is not an elementary divisor domain

This Lean 4 / Mathlib project formalizes *A Bézout domain that is not an elementary divisor domain* by **Christian Hägg and Anders Mörtberg**. Numbered references below and in the Lean sources refer to that paper, which is distributed separately.

Repository: [Zelaron/bezout-counterexample-lean](https://github.com/Zelaron/bezout-counterexample-lean). The formalization constructs a Bézout domain and proves that the explicit matrix

```text
    [ 1 + x    y   ]
M = [   y    1 - x ]
```

has no Smith normal form over it. The obstruction comes from the Möbius line bundle on the real unit circle, preserved through a sequence of principalization extensions with compact, connected fibers.

The main result is `BezoutCounterexample.main_theorem` in [MainTheorem.lean](BezoutCounterexample/MainTheorem.lean):

```lean
∃ (R : Type) (_ : CommRing R),
  IsDomain R ∧ IsBezout R ∧ ¬ IsElementaryDivisorDomain R
```

`IsBezout` is Mathlib’s predicate. The elementary-divisor predicate is defined in [Basic.lean](BezoutCounterexample/Basic.lean) using invertible row and column operations and the usual diagonal divisibility condition.

## Scope and statement correspondence

- [All 19 numbered statements and their Lean declarations](docs/STATEMENTS.md)
- [Source provenance](docs/PROVENANCE.md)

Every numbered theorem, lemma, proposition, definition, notation, and construction of this version of the paper has a corresponding formalization. Multi-part results are sometimes split into several declarations. Additional consequences used in the proofs are also proved.

Theorem 3.3(2) states the **polynomial-localization case** of the cited smooth-invariance theorem. This is the case needed here. Theorem 3.6 uses the affine vertex and scaling proof. General smooth-morphism invariance and algebraic-stack invariance are outside the stated scope. Lemma 3.5(5) includes the full **ring isomorphism** with the associated graded ring, with its homogeneous multiplication explicitly verified.

## Dependencies

- **Lean 4.34.1**, pinned in `lean-toolchain`.
- **Mathlib v4.34.1**, pinned by `lake-manifest.json` to commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Python 3 for the sequential verification script.

No project-specific axioms, proof placeholders, or native decision procedures are used. The axiom audit permits only Lean’s standard `propext`, `Classical.choice`, and `Quot.sound`.

## Build and verify

With [elan](https://github.com/leanprover/elan) installed, run from this directory:

```bash
lake exe cache get && python3 scripts/check.py --replay
```

This fetches the pinned Mathlib dependencies and their compiled cache, then:

1. Validates the statement map and scans mathematical sources for placeholders and unchecked mechanisms.
2. Compiles all project modules in dependency order, using one Lean worker and a 12 GiB Lean memory limit. Unchanged project artifacts are reused only when source and dependency fingerprints match.
3. Audits the transitive axioms of every declaration defined in a project module, including generated helpers.
4. Replays each project module through the Lean kernel using the distribution’s `LeanChecker.replayFromImports`, sequentially.
5. Writes the verification report, declaration inventory, and source hashes under `verification/`.

For a rebuild of every project source, ignoring the project fingerprint cache:

```bash
python3 scripts/check.py --clean --replay
```

Ordinary `lake build` is also supported by the package configuration. The script is preferable on a shared machine: it lowers its scheduling priority, uses one CPU on Linux, and avoids asking Lake to rebuild already cached dependencies. Loading the full Mathlib import needs roughly 7 GiB of resident memory on the checked toolchain.

Kernel replay checks project declarations against the pinned imported dependencies. It uses Lean’s kernel, not an independently implemented proof checker. Its small wrapper is [scripts/Replay.lean](scripts/Replay.lean); the axiom audit is [scripts/AxiomAudit.lean](scripts/AxiomAudit.lean). The replay wrapper uses Lean’s IO interface; it introduces no mathematical declarations or assumptions.

The source distribution contains no dependency cache, compiled artifacts, logs, or generated verification reports. Running the command above recreates them under `.lake/` and `verification/`, both ignored by Git.

The article is not required for compilation, the axiom audit, or kernel replay. If you have its source separately, you can also check its numbered-statement inventory against the statement map:

```bash
python3 scripts/check.py --replay --paper ../bezout-counterexample.tex
```

This optional check records the article’s SHA-256 hash in the generated report. The inventory and declaration checks supplement the mathematical comparison documented in [docs/STATEMENTS.md](docs/STATEMENTS.md); they do not by themselves establish that informal statements match Lean types.

The 43 Lean source modules were compiled and replayed through the Lean kernel on roos before this source-only distribution was prepared. The audit covered 2,804 declarations and found only the three standard axioms listed above. The mathematical Lean sources are unchanged in this distribution; rerun the command above to generate a verification report for your checkout.

## Read the proof

The top-level files follow the paper:

| Paper | Main files |
|---|---|
| Definitions and initial matrix | `Basic.lean` |
| Real points, Möbius bundle, orientation descent | `RealPoints.lean`, `Mobius.lean` |
| Jouanolou rings and factoriality | `Jouanolou.lean`, `Factoriality.lean`, `SplitConormal.lean` |
| Marked centers and the weighted invariant | `MarkedCenter.lean`, `Invariant.lean` |
| Rees algebras, associated graded ring, strict decrease | `Rees.lean`, `AssociatedGraded.lean` |
| Principalization steps and termination | `Divisorial.lean`, `Torsor.lean`, `LengthControl.lean`, `PrincipalizationStar.lean` |
| Compact lift and principalization extension | `SphereBundle.lean`, `PrincipalizationExtension.lean` |
| Scheduled union, Bézout property, obstruction | `Construction.lean`, `MainTheorem.lean` |

The supporting algebraic proofs live in `BezoutCounterexample/Principalization/`. They prove the needed invariant, center, Rees, and torsor facts; these are not introduced as axioms. Proof comments explain the mathematical steps and connect the supporting machinery to the statements in the paper.

To use the result from another Lean file:

```lean
import BezoutCounterexample

#check BezoutCounterexample.main_theorem
#print axioms BezoutCounterexample.main_theorem
```

## Acknowledgment

OpenAI’s GPT-6 Astra (via Codex) was used in preparing the article and its Lean formalization.

## License

[MIT](LICENSE), copyright Christian Hägg and Anders Mörtberg, 2026.
