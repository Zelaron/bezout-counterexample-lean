# Statement correspondence

This map covers every numbered theorem, lemma, proposition, definition, notation, and construction in *A Bézout domain that is not an elementary divisor domain* by Christian Hägg and Anders Mörtberg. The article is distributed separately. The human comparison of hypotheses and conclusions is recorded below. `scripts/check.py` checks that the listed declarations are present in the axiom audit. With `--paper PATH`, it also compares the article’s label inventory and records its SHA-256 hash; those mechanical checks supplement the mathematical comparison.

| Number | Paper label | Statement | Lean source |
|---|---|---|---|
| 1.1 | `thm:main` | A Bézout domain that is not an elementary divisor domain | [MainTheorem.lean](../BezoutCounterexample/MainTheorem.lean) |
| 2.1 | `lem:orientation-descent` | Orientation descends along compact monotone surjections | [Mobius.lean](../BezoutCounterexample/Mobius.lean) |
| 2.2 | `lem:monotone-composition` | Composition of monotone surjections | [Mobius.lean](../BezoutCounterexample/Mobius.lean) |
| 3.1 | `lem:jouanolou` | Jouanolou rings, all five parts | [Jouanolou.lean](../BezoutCounterexample/Jouanolou.lean) |
| 3.2 | `def:marked-centre` | Marked centers, weighted ideals, admissibility | [MarkedCenter.lean](../BezoutCounterexample/MarkedCenter.lean) |
| 3.3 | `thm:invariant` | Weighted invariant, all five parts | [Invariant.lean](../BezoutCounterexample/Invariant.lean) |
| 3.4 | `not:rees` | Extended Rees algebra and weak transform | [Rees.lean](../BezoutCounterexample/Rees.lean) |
| 3.5 | `lem:rees` | Rees algebra properties, all five parts | [Rees.lean](../BezoutCounterexample/Rees.lean) |
| 3.6 | `thm:drop` | Strict decrease on the exceptional divisor away from the vertex | [Rees.lean](../BezoutCounterexample/Rees.lean) |
| 3.7 | `lem:derivations` | Preservation of the center and bound from derivations | [Rees.lean](../BezoutCounterexample/Rees.lean) |
| 4.1 | `lem:divisorial` | Divisorial step | [Divisorial.lean](../BezoutCounterexample/Divisorial.lean) |
| 4.2 | `lem:torsor` | Torsor smoothness, factoriality, injection, factorization | [Torsor.lean](../BezoutCounterexample/Torsor.lean) |
| 4.3 | `lem:torsor-invariant` | Nonzero weak transform and complexity decrease | [Torsor.lean](../BezoutCounterexample/Torsor.lean) |
| 4.4 | `lem:length-control` | Preservation of the dimension and derivation bound | [LengthControl.lean](../BezoutCounterexample/LengthControl.lean) |
| 4.5 | `lem:sphere-bundle` | Compact normalized lift with connected fibers | [SphereBundle.lean](../BezoutCounterexample/SphereBundle.lean) |
| 4.6 | `prop:principalization-extension` | Principalization extension for two elements | [PrincipalizationExtension.lean](../BezoutCounterexample/PrincipalizationExtension.lean) |
| 5.1 | `construction:ring` | Scheduled construction and increasing union | [Construction.lean](../BezoutCounterexample/Construction.lean) |
| 5.2 | `prop:bezout-domain` | The constructed ring is a Bézout domain | [Construction.lean](../BezoutCounterexample/Construction.lean) |
| 5.3 | `lem:key-obstruction` | No five elements satisfy the matrix identity | [MainTheorem.lean](../BezoutCounterexample/MainTheorem.lean) |

## 1.1: A Bézout domain that is not an elementary divisor domain

`main_theorem`, `not_hasSmithNormalForm`.

## 2.1: Orientation descends along compact monotone surjections

`orientation_descent`.

## 2.2: Composition of monotone surjections

`IsMonotoneSurjection.comp`.

## 3.1: Jouanolou rings, all five parts

`Jou.tensorEquiv`, `Jou.quotientEquiv`, `Jou.isLocalization_map`, `Jou.awayEquiv`, `Jou.isDomain`, `Jou.algebraMap_injective`, `Jou.formallySmooth`, `Jou.smooth`, `Jou.ufd`.

Parts (1)–(5) are separate declarations; the row length is `r + 1` when eliminating a coordinate.

## 3.2: Marked centers, weighted ideals, admissibility

`MarkedCenter`, `MarkedCenter.F`, `MarkedCenter.IsAdmissible`, `MarkedCenter.weights`, `IsRegularSystemOfParameters.exists_chart`.

The definition uses regular parameters, not a stronger chart hypothesis. The bridge to dual derivations is proved.

## 3.3: Weighted invariant, all five parts

`theorem_3_3_1`, `inv_map_eq_of_localization_polynomial`, `maxinv_spec`, `theorem_3_3_3`, `theorem_3_3_4`, `Γ`, `inv_mem_Γ`, `Γ_wellFoundedOn`, `next_weight_form`.

Part (2) is exactly the polynomial-localization case in the revised paper. General smooth morphisms and stacks are not claimed. Part (5) uses well-foundedness of the strict reverse lexicographic order; totality comes from lexicographic order.

## 3.4: Extended Rees algebra and weak transform

`ReesData`, `ReesData.𝓕`, `ReesData.𝓡`, `ReesData.s`, `ReesData.𝓡plus`, `ReesData.Iw`, `ReesData.G`, `ReesData.span_G`.

## 3.5: Rees algebra properties, all five parts

`ReesData.𝓕_of_nonpos`, `ReesData.𝓕_one`, `ReesData.pow_le_𝓕`, `ReesData.I_le_𝓕`, `ReesData.map_I_eq`, `ReesData.map_𝔭_le`, `ReesData.𝓕_eq_sum`, `ReesData.𝓡_eq_adjoin`, `ReesData.𝓡plus_eq_span`, `ReesData.isLocalization_away_s`, `ReesData.isLocalization_rees`, `ReesData.rees_presentation`, `ReesData.rees_loc_eq_top`, `ReesData.rees_smooth_domain`, `ReesData.quotientSRingEquiv`, `ReesData.initialForm_mul`, `ReesData.gradedAddEquiv_apply`, `ReesData.associatedGraded_isDomain`, `ReesData.prime_s`.

Part (5) also uses AssociatedGraded.lean: the direct sum has its usual addition and homogeneous multiplication, and the identification is a ring isomorphism, not merely a module isomorphism. Parts (3)–(4) express localization by its universal property, equivalent to the displayed rings/tensor products.

## 3.6: Strict decrease on the exceptional divisor away from the vertex

`ReesData.drop`.

The affine vertex, local-center, and rational scaling argument is in Principalization/Vertex.lean, ReesVertex.lean, and Drop.lean, matching the revised proof.

## 3.7: Preservation of the center and bound from derivations

`deriv_mem_maxCenter`, `ReesData.deriv_mem_𝓕`, `numNonzero_inv_add_le`.

The last conclusion is written as `number of nonzero weights + m ≤ dim A`, equivalent to the paper’s subtraction bound.

## 4.1: Divisorial step

`PrincipalizationData.divisorial_e`, `PrincipalizationData.divisorial_𝔭_eq`, `PrincipalizationData.divisorial_le`, `PrincipalizationData.divisorial_I_eq`, `PrincipalizationData.divisorial_decrease`.

## 4.2: Torsor smoothness, factoriality, injection, factorization

`PrincipalizationData.torsor_spec`.

## 4.3: Nonzero weak transform and complexity decrease

`PrincipalizationData.torsor_invariant`.

## 4.4: Preservation of the dimension and derivation bound

`Star`, `PrincipalizationData.length_control_divisorial`, `PrincipalizationData.length_control_torsor`.

## 4.5: Compact normalized lift with connected fibers

`PrincipalizationData.E`, `PrincipalizationData.E_spec`, `PrincipalizationData.sphereBundle`, `PrincipalizationData.sphere_bundle`.

## 4.6: Principalization extension for two elements

`principalization_extension`.

The exported statement is for `a,b` not both zero. `principalization_extension_ideal` and `principalization_star` prove the auxiliary stronger assertions used in its proof.

## 5.1: Scheduled construction and increasing union

`pairing`, `left_le_pairing`, `Construction.η_surjective`, `Construction.pairAt_eq`, `Construction.stage`, `Construction.step_of_eq_zero`, `Construction.step_of_ne_zero`, `Construction.incl_injective`, `Construction.isCompact_K`, `Construction.isMonotoneSurjOn_incl`, `R`, `R.of_injective`, `R.exists_of`.

The increasing union is Mathlib’s ring direct limit; injectivity and representation at finite stages are proved. The construction includes the zero cases and coprime-factor reduction.

## 5.2: The constructed ring is a Bézout domain

`bezout_domain`, `R.isDomain`, `R.isBezout`.

## 5.3: No five elements satisfy the matrix identity

`key_obstruction`.

Exactly five elements and right-hand side `1`, as in the new article; no extra element or congruence modulo Δ.

## Numbered equations and the obstruction

`Basic.lean` defines `A₀`, `x`, `y`, `Δ`, and `M`. `Mobius.lean` proves `det_M`, `span_entries_M`, `M_sq`, `Mreal_cos_sin`, and `L₀_not_isOrientable`. `SphereBundle.lean` proves `s_norm`. `Construction.nonorientable` proves nonorientability at every stage. The union and the hypothetical Smith normal form are represented by `R` and `not_hasSmithNormalForm`.

## Conventions

- Ideals extend via `Ideal.map`; principal multiples use products with `Ideal.span {a}`.
- `Algebra.Smooth ℚ A` includes finite presentation, hence finite generation. `SmoothFactorialDomain` also records `CommRing`, `IsDomain`, and `UniqueFactorizationMonoid`.
- Weights and matrices are indexed from zero in Lean; weights are extended by zeros to `ℕ → ℚ`.
- Real points are actual ring homomorphisms to Mathlib’s real numbers with the evaluation topology. Orientability is the existence of a continuous nowhere-zero section of the specified image line.
- `IsBezout` is Mathlib’s predicate. `IsElementaryDivisorDomain` uses equivalence by invertible matrices and a diagonal divisibility chain, as in the paper.
