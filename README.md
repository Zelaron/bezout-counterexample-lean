# Lean formalization of *A countable Bézout domain without the elementary divisor property*

This Lake project (Lean 4 `v4.34.1`, Mathlib `v4.34.1`) formalizes the paper *A countable Bézout
domain without the elementary divisor property* by C. Hägg and A. Mörtberg
(`bezout-counterexample.tex`). Numbered references (Theorem 1.1, Proposition 4.6, …) in this
README and in the docstrings are to that paper.

With [elan](https://github.com/leanprover/elan) installed (the toolchain is pinned in
`lean-toolchain`):

```
lake exe cache get   # download the Mathlib build cache
lake build           # builds everything; no `sorry`, no `axiom`
```

## What is proved

Nothing in this project uses `sorry` or `axiom`, and no statement from the literature is assumed.
Every numbered result of the paper is formalized, in the generality in which the paper uses it,
and proved unconditionally; the only exception is the theorem of McGovern quoted in Remark 6.3,
which no proof uses. Among the results are Theorem 1.1
(`main_theorem`), Proposition 6.2 (`proposition_6_2`: `R` has Krull dimension at least two and is
not Noetherian) and Corollary 6.4 (`corollary_6_4`). `#print axioms` for every main theorem gives
only `propext`, `Classical.choice`, `Quot.sound`.

The paper quotes some results from the literature. The formalization proves them in the
generality in which the paper uses them:

* the properties of the weighted invariant of Abramovich–Temkin–Włodarczyk and Brais
  (Theorems 3.3 and 3.6), in `Principalization/`;
* the local structure of extended Rees algebras (quoted from Quek–Rydh in the proof of
  Lemma 3.5), `rees_formallySmooth` (`ReesSmooth.lean`);
* the criterion for formal smoothness by split conormal sequences (Stacks, Tag 031J), in the form
  `formallySmooth_quotient_of_dual` (`ReesSmooth.lean`);
* Nagata's criterion (§3.1; Stacks, Tag 0AFU), `UniqueFactorizationMonoid.of_isLocalization_away`
  (`Nagata.lean`);
* Couchot's theorem (§6.4), in the `2 × 2` case for domains that Corollary 6.4 needs:
  `hasSNF_two_of_countableCharacter` (`Couchot.lean`, following Fuchs–Salce III.6.5 and
  Chen–Sheibani, Lemma 5.1). Starting from `[[a, 0], [b, c]]`, alternate row and column Hermite
  reductions so that the `k`-th corner avoids the `k`-th maximal ideal containing `a`; the corner
  ideals increase, and their union cannot be proper, so some corner is a unit.

**Proposition 4.6** (`PrincipalizationExtension` in `Defs.lean`) is where the algebraic geometry
enters. It is proved as `Principalization.principalizationExtension`, following §§3–4: weighted
blowups (Abramovich–Temkin–Włodarczyk, in the presentation of Brais) carried out on affine rings,
namely Jouanolou torsors over extended Rees algebras:

* the invariant (`IsInv`, `InvAt`: lexicographically minimal weights of admissible marked centres),
  its smooth invariance, upper semicontinuity, the maximal locus and its components
  (`Invariant.lean`, `MaxLocus.lean`, `Transfer.lean`, `Globalize.lean`, …);
* the weighted extended Rees algebra of a component (`ReesGlobal.lean`, `ReesSmooth.lean`,
  `ReesVertex.lean`) and the drop of the invariant on the exceptional divisor (`Drop.lean`);
* the Jouanolou torsor `U = R[σ]/(∑ σᵢ yᵢ - 1)`, a smooth factorial domain (`Jouanolou.lean`,
  `Torsor.lean`), its invariants and components (`TorsorInv.lean`), the vertical derivations
  giving the length bound for termination (`TorsorDer.lean`), the divisorial case
  (`Divisorial.lean`), and the termination measure and induction (`Induction.lean`);
* the real points: a weighted sphere bundle `K' ⊆ U(ℝ)` that is compact and maps onto `K` with
  connected fibres (points, or continuous images of `ℝᵏ ∖ {0}`, `k ≥ 2`) (`RealPts.lean`).

`coprimePairPE_holds : CoprimePairPE` and `main_theorem` (in `MainTheorem.lean`) are derived from
`Principalization.principalizationExtension`; the conditional versions
`main_theorem_of_coprimePair`, `main_theorem_of_principalization` are kept. Everything
parametrized by `hPE : CoprimePairPE` (Construction 5.1, Proposition 5.2, …) can be instantiated
with `coprimePairPE_holds`.

`NOTES.md` collects mathematical observations made during the formalization, including the
strengthenings behind Remarks 4.7 and 5.4.

## Correspondence with the paper

| paper | Lean (namespace `BezoutCounterexample`) |
|---|---|
| §1: equivalence, Smith normal form, elementary divisor domains | `MatrixEquivalent`, `IsSmithNormalForm`, `HasSmithNormalForm`, `IsElementaryDivisorDomain`, `IsElementaryDivisorDomain.isBezout` |
| (1.1) initial data | `A₀`, `x`, `y`, `Δ`, `M` |
| **Theorem 1.1** (`thm:main`) | `main_theorem`, `R.not_hasSmithNormalForm`, `R.not_isElementaryDivisorDomain` |
| (2.1) `det M = -Δ`, `(1+x, y, 1-x) = A₀`, `M² - 2M = ΔI` | `det_M`, `span_entries_M`, `M_sq` |
| §2.1 real points, compactness criterion | `RealPt`, `RealPt.isCompact_of_forall_bounded`, `RealPt.forall_bounded_of_gen` |
| §2.2 `½M(z)` has rank one, (2.2) half-angle formula, `L₀` is nonorientable | `Mreal_half_idempotent`, `Mreal_rank`, `Mreal_cos_sin`, `L₀_nonorientable` |
| Lemma 2.1 (`lem:orientation-descent`) | `orientation_descent` |
| Lemma 2.2 (`lem:monotone-composition`) | `IsMonotoneSurjection.comp`, `IsMonotoneSurjection.isConnected_preimage` |
| §3.1 factoriality | `Nagata.lean` |
| Lemma 3.1 (`lem:jouanolou`) | `Jouanolou.lean` (`Jou.isDomain`, `Jou.formallySmooth`, `Jou.ufd`, …) |
| Definition 3.2, Theorem 3.3 (`thm:invariant`) | `Principalization/{Chart, Duality, Centre, Transfer, Local, Spread, Globalize, Invariant, MaxLocus}.lean` |
| Notation 3.4, Lemma 3.5 (`lem:rees`) | `Principalization/{Rees, ReesSmooth, ReesGlobal, ReesVertex}.lean` |
| Theorem 3.6 (`thm:drop`) | `Principalization/{Vertex, Drop}.lean` (`drop`) |
| Lemma 3.7 (`lem:derivations`) | `Principalization/Stable.lean`, `deriv_mem_compF` |
| Lemma 4.1 (`lem:divisorial`) | `Principalization/Divisorial.lean` |
| Lemmas 4.2, 4.3 (`lem:torsor`, `lem:torsor-invariant`) | `Principalization/{Torsor, TorsorInv}.lean` |
| Lemma 4.4 (`lem:length-control`) | `Principalization/TorsorDer.lean` (`VertOK`, `DimOK`) |
| Lemma 4.5 (`lem:sphere-bundle`) | `Principalization/RealPts.lean` (`torsorK`, `torsorRealPts`) |
| **Proposition 4.6** (`prop:principalization-extension`) | `PrincipalizationExtension` (statement), `Principalization.principalizationExtension` (proof; `Induction.lean`, `RealPts.lean`) |
| Remark 4.7 (`rem:strong`) | `Principalization.principalizationExtension_strong` (`Strong.lean`) |
| Construction 5.1, (5.1) | `stage`, `step`, `R` (a direct limit; `Construction.lean`) |
| Proposition 5.2 (`prop:bezout-domain`) | instances `IsBezout (R hPE)`, `IsDomain (R hPE)`, `Countable (R hPE)`, `CharZero (R hPE)`; `R.Δ_ne_zero`, `R.Δ_not_isUnit`, `R.algebraicIndependent` |
| (5.2) `L_n` is nonorientable | the field `Stage.nonorientable` of every `stage hPE n`, via `nonorientable_pullback` |
| Lemma 5.3 (`lem:key-obstruction`) | `R.no_unit_value_mod` (`MainTheorem.lean`) |
| Remark 5.4 (`rem:abstract`) | `Abstract.lean`: `IsMobiusTower.main`, `isMobiusTower_of_sequence`, `HasMobiusTest`, `HasOddLoop` |
| Proposition 6.1 (`prop:quotient-module`) | `quotient_module` (`QuotientModule.lean`) |
| Proposition 6.2 (`prop:dimension`) | `R.exists_prime_lt_maximal`, `R.two_le_ringKrullDim`, `R.not_isNoetherianRing`, `proposition_6_2`; for every run of Construction 5.1: `IsMobiusTower.two_le_ringKrullDim` (`Dimension.lean`) |
| Remark 6.3 (`rem:dimension`) | McGovern's theorem is not formalized |
| §6.3 explicit first extension | `Explicit.*` (`ExplicitAlgebra.lean`, `ExplicitTopology.lean`; see below) |
| §6.4 countable character, semihereditary rings | `HasCountableCharacter`, `IsSemihereditary`, `IsBezout.isSemihereditary` |
| Corollary 6.4 (`cor:not-countable-character`) | `corollary_6_4`, `R.not_hasCountableCharacter`; the local version after it: `R.not_countable_maximal` (`Couchot.lean`) |
| §6.4 example `ℚ[t, z₁, z₂, …]` | `exampleC_countable`, `exampleC_uncountable`, `maxIdealε_*` |
| Proposition 6.5 (`prop:countable-reduction`) | `countable_reduction` |

§6.3 in detail (namespace `BezoutCounterexample.Explicit`):
`A* = S[t]`, `S = ℚ[u,v,r,s]/(ru+sv-1)`;
`span_u_v` (`(u,v) = A*`), `map_span_eq` (`(x-1,y)A* = tA*`), `phi_injective`,
`f_prime`/`IsDomain S` (integrality, via Gauss's lemma), `u_prime` (`A*/(u)` is a domain),
`equivSu` (`S[1/u] ≅ ℚ[u,s,v][1/u]`), `UniqueFactorizationMonoid S` (factoriality, via
Nagata's criterion), `Algebra.Smooth ℚ S` and `Algebra.Smooth ℚ Astar` (smoothness, via the cover
`D(u) ∪ D(v)`), `isCompact_Kstar`, `isMonotoneSurjOn_Kstar` (fibres: points, and a circle over
`(1,0)`), `Kstar_nonorientable`; together, `principalizationExtension_example` (the conclusion of
Proposition 4.6 for `A = ℚ[x,y]`, `I = (x-1, y)`, `K = K₀`).

General tools proved along the way: `UniqueFactorizationMonoid.of_isLocalization` (localizations of
UFDs are UFDs) and `UniqueFactorizationMonoid.of_isLocalization_away` (**Nagata's criterion**), in
`Nagata.lean`; `HasSmithNormalForm.map`; the trace argument `exists_factorization_of_free`.

## Formalization choices

* `Spec(A)(ℝ)` is `RealPt A := A →+* ℝ` with the weak topology (every evaluation `z ↦ z a` is
  continuous), as in §2.1. For finitely generated `ℚ`-algebras this is the Euclidean topology.
* Real line bundles only appear as the line field `z ↦ im M(z)`; "orientable" means "has a
  continuous nowhere vanishing section" (`LineFieldOrientable`), as in §2.2.
* "Smooth finitely generated factorial `ℚ`-domain" is `Algebra.Smooth ℚ A` (which includes finite
  presentation) together with `IsDomain` and `UniqueFactorizationMonoid` (`SmoothFactorialDomain`).
* "Constant rank one" in Proposition 6.1 is stated as `dim κ(p) ⊗ ΠB² = 1` for every prime `p`
  (`Ideal.Fiber`).
* Smith normal form is stated as "diagonal with `d₀ ∣ d₁ ∣ ⋯`". Since `0 ∣ a` forces `a = 0`, this
  is equivalent to the paper's "nonzero diagonal entries first, dividing each other".
* `R hPE` is built from one run of Construction 5.1 (`Classical.choose` in Proposition 4.6, and a
  fixed enumeration of the pairs). Every other run is covered by `isMobiusTower_of_sequence`
  (Remark 5.4).
* The ring `A*` of §6.3 is built as `MvPolynomial (Fin 1) S` with `S = ℚ[u,s,r,v]/(ru+sv-1)`, which
  is canonically `ℚ[t,u,v,r,s]/(ru+sv-1)`.

## Unused code

Every module in `BezoutCounterexample/` is needed for a result listed above; modules from
earlier routes to Proposition 4.6 have been removed. About 70 small declarations (roughly 300 of
about 23,000 lines) are not used by any listed result. Most are simp or API lemmas; a few are
documented extras (`HasMobiusTest.comap`, `IsMobiusTower.of_cofinal`, `hasMobiusTest_A₀`).

## License

MIT; see `LICENSE`.
