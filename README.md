# Lean formalization of *A countable Bézout domain that is not an elementary divisor domain*

This Lake project (Lean 4 `v4.34.1`, Mathlib `v4.34.1`) formalizes the paper
*A countable Bézout domain that is not an elementary divisor domain* by C. Hägg and
A. Mörtberg. Numbered references (Theorem 1.1, Lemma 3.5, …) are to that paper.

With [elan](https://github.com/leanprover/elan) installed (the toolchain is pinned in
`lean-toolchain`):

```
lake exe cache get   # download the Mathlib build cache
lake build           # builds everything; no `sorry`, no `axiom`
```

A clean build of the project (on top of the Mathlib cache) takes one to two hours on an 8-core
laptop. It prints no errors and no warnings, including linter and deprecation warnings.

To check the axioms, compile a file containing

```lean
import BezoutCounterexample
#print axioms BezoutCounterexample.main_theorem
```

with `lake env lean <file>`. The output is `[propext, Classical.choice, Quot.sound]`.

## What is proved

Every numbered result of the paper (theorems, propositions, lemmas, the corollary, the
definition, the notation, the construction, and the numbered equations) is stated in Lean in the
language of the paper and proved. The proofs follow the paper's arguments except where listed
under *Deviations* below. There is no `sorry` and no `axiom`. `#print axioms` for the main
results gives only `propext`, `Classical.choice`, `Quot.sound`.

**Theorem 1.1** (`thm:main`) is `BezoutCounterexample.main_theorem` (`MainTheorem.lean`):

```lean
theorem main_theorem :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (ι : A₀ →+* R),
      Countable R ∧ IsBezout R ∧ Function.Injective ι ∧ ι Δ ≠ 0 ∧ ¬ IsUnit (ι Δ) ∧
      ¬ HasSmithNormalForm (M.map ι) ∧ CharZero R ∧ ¬ IsElementaryDivisorDomain R
```

Here `A₀ = MvPolynomial (Fin 2) ℚ`, `x = X 0`, `y = X 1`, `Δ = x ^ 2 + y ^ 2 - 1` and
`M = !![1 + x, y; y, 1 - x]` (`Basic.lean`). `HasSmithNormalForm` and `IsElementaryDivisorDomain`
are defined in `Basic.lean` exactly as in §1 (equivalence `P F Q = G` with `P, Q` invertible; a
diagonal matrix whose nonzero diagonal entries come first and form a divisibility chain).

The paper quotes several results from the literature. These are proved here too, in the
generality the paper needs:

* the properties of the weighted invariant of Abramovich–Temkin–Włodarczyk and Brais
  (**Theorem 3.3**; part (2) in the special case the paper uses, see *Deviations*);
* the strict decrease of the invariant (**Theorem 3.6**);
* the local presentation of the extended Rees algebra (Quek–Rydh, Proposition 5.2.2; used in
  **Lemma 3.5(4)**);
* the split-conormal criterion for formal smoothness (Stacks, Tag 031J) and **Nagata's
  criterion** (Stacks, Tag 0AFU); that polynomial rings over UFDs are UFDs (Stacks, Tag 0BC1)
  is in Mathlib;
* **Couchot's theorem** and **[CS, Lemma 5.1]**, in the special case used in §6.4 (`2 × 2`
  matrices over Bézout domains).

Not formalized: Remark 6.3 (it quotes a theorem of McGovern, and no proof uses it), and a few
explanatory asides (see *Deviations* below).

## Structure

The files in `BezoutCounterexample/` follow the paper section by section (the *article layer*).
The directory `BezoutCounterexample/Principalization/` is the *engine*. It formalizes the weighted
invariant in terms of *charts* (families of elements whose differentials form a basis of `Ω`,
with dual derivations), Method-1 runs of Brais, extended Rees algebras, Jouanolou torsors and
their real points. The article layer states every result in the language of the paper: regular
systems of parameters, Krull dimension, invariants as weight vectors in `ℚ^ℕ`, the maximal
invariant, the components of the maximal locus, and so on. It derives these results from the
engine through bridging lemmas (`MarkedCenter.lean`, `Invariant.lean`), and it carries out the
arguments of §4–§6 itself.

| file | paper |
|---|---|
| `Basic.lean` | §1: Bézout domains, equivalence of matrices, Smith normal form, elementary divisor domains, (1.1) |
| `RealPoints.lean` | §2.1: real points, the compactness criterion, monotone surjections |
| `Mobius.lean` | (2.1), §2.2: the line bundles `L_{X,Y}`, `K₀`, `L₀`, (2.2), Lemmas 2.1 and 2.2 |
| `Factoriality.lean` | §3 (smooth finitely generated factorial `ℚ`-domains), §3.1 |
| `SplitConormal.lean`, `Jouanolou.lean` | §3.2, Lemma 3.1 |
| `MarkedCenter.lean` | §3.3: the regular local rings `A_𝔪`, Definition 3.2, the order `⪯` |
| `Invariant.lean` | Theorem 3.3 |
| `Rees.lean` | Notation 3.4, Lemma 3.5, Theorem 3.6, Lemma 3.7 |
| `Divisorial.lean` | the setting of §4, Lemma 4.1 |
| `Torsor.lean` | §4.2, Lemmas 4.2 and 4.3 |
| `LengthControl.lean` | §4.3: `(⋆_N)`, Lemma 4.4 |
| `SphereBundle.lean` | Lemma 4.5, (4.1) |
| `PrincipalizationStar.lean`, `PrincipalizationExtension.lean` | Proposition 4.6 |
| `PrincipalizationStrong.lean` | Remark 4.7 |
| `Construction.lean` | Construction 5.1, (5.1), Proposition 5.2, (5.2) |
| `MainTheorem.lean` | Lemma 5.3, (5.3), Theorem 1.1 |
| `QuotientModule.lean` | Proposition 6.1, (6.1) |
| `Dimension.lean` | Proposition 6.2 |
| `Explicit.lean`, `ExplicitRealPoints.lean` | §6.3 |
| `CountableCharacter.lean` | §6.4, Corollary 6.4 |
| `CountableReduction.lean` | Proposition 6.5 |

The engine, in dependency order: `Chart`, `Duality`, `Centre` (marked centres, uniqueness of the
maximal admissible centre), `Transfer` (Method-1 runs), `Local`, `Spread`, `Globalize` (local
structure of the invariant), `Stable` (Lemma 3.7), `Rees`, `Vertex`, `DerivExt`, `ReesSmooth`
(smoothness of the local weighted Rees algebra), `Invariant`, `MaxLocus` (Theorem 3.3 in chart
language), `ReesGlobal`, `ReesVertex` (Lemma 3.5), `Drop` (Theorem 3.6), `Torsor`, `TorsorInv`,
`TorsorDer` (Lemmas 4.2–4.4), `Divisorial` (Lemma 4.1), `Induction` (the termination measure),
`RealPts` (Lemma 4.5), `Strong` (Remark 4.7).

## Correspondence with the paper

All names are in the namespace `BezoutCounterexample`. Lean indices start at `0`, so the weights
`e₁, e₂, …` of the paper are `e 0, e 1, …`.

| paper | Lean |
|---|---|
| §1: Bézout domains | `IsBezout` (Mathlib), `isBezout_iff_span_pair_isPrincipal` |
| §1: equivalent matrices, Smith normal form, elementary divisor domains | `MatrixEquivalent`, `IsSmithNormalForm`, `isSmithNormalForm_iff_chain`, `HasSmithNormalForm`, `IsElementaryDivisorDomain` |
| §1: every elementary divisor domain is Bézout | `IsElementaryDivisorDomain.isBezout` |
| (1.1) | `A₀`, `x`, `y`, `Δ`, `M`, `algebraicIndependent_x_y` |
| Theorem 1.1 | `main_theorem` |
| (2.1) | `det_M`, `span_entries_M` (via `one_add_x_add_one_sub_x`), `M_sq` |
| §2.1: `Spec(A)(ℝ)` and `f^*` | `RealPt`, `RealPt.comap`, `RealPt.continuous_comap` |
| §2.1: real points of `ℚ[a₁, …, a_m]`; the compactness criterion | `RealPt.isEmbedding_evalGens`, `RealPt.range_evalGens`; `RealPt.isCompact_iff` |
| §2.1: monotone surjections | `IsMonotoneSurjection`, `IsMonotoneSurjOn` |
| §2.2: `M(X, Y)`; `½ M(X(z), Y(z))` is an idempotent of rank one | `Mreal`, `M_map`; `half_Mreal_idempotent`, `half_Mreal_rank` |
| §2.2: `L_{X,Y}`, the line subbundle, orientability, pullbacks | `lineBundle`, `finrank_lineBundle`, `lineBundle_locally_trivial`, `IsOrientable`, `lineBundle_comp` |
| §2.2: `K₀` is the unit circle; `L₀` | `K₀`, `K₀HomeomorphCircle`, `isCompact_K₀`; `X₀`, `Y₀` |
| (2.2); `L₀` is nonorientable | `Mreal_cos_sin`; `L₀_not_isOrientable` |
| Lemma 2.1 | `orientation_descent` (and `not_isOrientable_comp`, `not_isOrientable_pullback`) |
| Lemma 2.2 | `IsMonotoneSurjection.comp`, `IsMonotoneSurjOn.trans` (via `IsMonotoneSurjection.isConnected_preimage`) |
| §3: smooth finitely generated factorial `ℚ`-domains | `SmoothFactorialDomain` |
| §3.1 | `polynomial_ufd`, `mvPolynomial_ufd`, `UniqueFactorizationMonoid.of_isLocalization_away` (Nagata's criterion), `laurentPolynomial_ufd`, `prime_laurentPolynomial_C` |
| §3.2: `q_c`, `J_B(c)`, the real points of `J_B(c)` | `Jou.rel`, `Jou.J`, `Jou.σ`, `Jou.realPtEquiv` |
| Lemma 3.1(1) | `Jou.tensorEquiv`, `Jou.quotientEquiv`, `Jou.isLocalization_map` |
| Lemma 3.1(2) | `Jou.isLocalization_elim`, `Jou.awayEquiv` |
| Lemma 3.1(3) | `Jou.isDomain`, `Jou.algebraMap_injective` |
| Lemma 3.1(4) | `Jou.formallySmooth` (by the split-conormal criterion `formallySmooth_quotient_of_dual`), `Jou.smooth` |
| Lemma 3.1(5) | `Jou.ufd` |
| §3.3: `A_𝔪` is regular of dimension `dim A` with finite residue field; regular systems of parameters; `dx₁, …, dxₙ` is a basis; dual derivations | `isRegularLocalRing_localization`, `ringKrullDim_localization`, `finite_residueField`, `IsRegularSystemOfParameters`, `exists_isRegularSystemOfParameters`, `IsRegularSystemOfParameters.exists_basis`, `IsRegularSystemOfParameters.exists_dual` |
| Definition 3.2 | `MarkedCenter`, `MarkedCenter.F`, `MarkedCenter.IsAdmissible` |
| §3.3: weight vectors in `ℚ^ℕ`, `⪯`, `≺`, `ord_𝔪` | `MarkedCenter.weights`, `WeightLE` (notation `⪯`), `WeightLT` (notation `≺`), `numNonzero`, `ord` |
| Theorem 3.3(1) | `IsInvariant`, `inv`, `maxCenter`, `isInvariant_inv`, `MarkedCenter.F_eq_maxCenter`, `inv_le_one`, `inv_zero_eq_one_div_ord`, `exists_inv_zero_eq`, `inv_zero_le_of_le_pow`; bundled: `theorem_3_3_1` |
| Theorem 3.3(2) | `inv_map_eq_of_localization_polynomial` |
| Theorem 3.3(3) | `maxinv`, `components`, `numComponents`, `theorem_3_3_3` |
| Theorem 3.3(4) | `globalCenter`, `theorem_3_3_4` |
| Theorem 3.3(5), and the justification of the enlargement of `Γ` | `Γ`, `inv_mem_Γ`, `Γ_wellFoundedOn`; `next_weight_form` |
| Notation 3.4 | `ReesData`, with `ReesData.𝓕`, `𝓡`, `s`, `𝓡plus` (`𝓡₊`), `Iw`, `G` |
| Lemma 3.5(1) | `ReesData.𝓕_of_nonpos`, `𝓕_one`, `pow_le_𝓕`, `I_le_𝓕`, `map_I_eq`, `map_𝔭_le` |
| Lemma 3.5(2) | `ReesData.𝓕_eq_sum`, `𝓡_eq_adjoin`, `𝓡plus_eq_span` |
| Lemma 3.5(3) | `ReesData.isLocalization_away_s` |
| Lemma 3.5(4) | `ReesData.isLocalization_rees`, `rees_presentation`, `rees_loc_eq_top`, `rees_smooth_domain` |
| Lemma 3.5(5) | `ReesData.mono_mem_span_s_iff`, `quotientSEquiv`, `mul_not_mem_𝓕`, `isDomain_quotient_s`, `prime_s` |
| Theorem 3.6 | `ReesData.drop` |
| Lemma 3.7(1) | `deriv_mem_maxCenter`, `ReesData.deriv_mem_𝓕` |
| Lemma 3.7(2) | `numNonzero_inv_add_le` |
| §4: the setting (`π`, `k`, `c(I)`) | `PrincipalizationData`, `ReesData.exists_prime_mem`, `numComponents` |
| Lemma 4.1 | `PrincipalizationData.divI₁`, `divisorial_e`, `divisorial_𝔭_eq`, `divisorial_le`, `divisorial_I_eq`, `divisorial_sup`, `divisorial_inv_eq`, `divisorial_decrease` |
| §4.2: `h`, `U`, `I₁` | `PrincipalizationData.h`, `jdeg`, `g`, `U`, `I₁` |
| Lemma 4.2 | `PrincipalizationData.torsor_spec` (and `torsorSFD`) |
| Lemma 4.3 | `PrincipalizationData.torsor_invariant` |
| §4.3: `(⋆_N)` | `Star`, `Star.numNonzero_inv_le`, `star_initial` |
| Lemma 4.4 | `PrincipalizationData.length_control_divisorial`, `length_control_torsor` |
| Lemma 4.5 | `PrincipalizationData.E`, `sphereBundle`, `sphere_bundle` |
| (4.1) | `PrincipalizationData.ν`, `s_norm`, `ν_pos_iff` |
| Proposition 4.6 | `principalization_extension`; the stronger assertion in its proof: `principalization_star` (well-founded induction on `ComplexityLT`) |
| Remark 4.7 | `principalization_extension_strong` |
| Construction 5.1 | `pairing`, `left_le_pairing`, `Construction.A`, `Construction.K`, `Construction.incl`, `Construction.η`, `Construction.pairAt`, `Construction.pairAt_eq`, `Construction.step` (`trivialStep`, `principalizationStep`), `Construction.principalizationStep_map_span`, `Construction.span_pairAt_map_isPrincipal`, `Construction.isCompact_K`, `Construction.incl_injective`, `Construction.isMonotoneSurjOn_incl` |
| (5.1) | `R` (with `R.of`, `R.of_injective`, `R.ι`) |
| Proposition 5.2 | `bezout_domain` (`R.countable`, `R.isDomain`, `R.isBezout`, `R.charZero`, `R.algebraicIndependent`, `R.Δ_ne_zero`, `R.Δ_not_isUnit`) |
| (5.2) | `Construction.nonorientable` |
| Lemma 5.3 | `key_obstruction` |
| (5.3) and the proof of Theorem 1.1 | `not_hasSmithNormalForm`, `not_isElementaryDivisorDomain` |
| Proposition 6.1 | `quotient_module` (with `PiMat` for `Π`, `HasConstantRankOne`, `PiMat_idempotent`, `PiMat_hasConstantRankOne`, `imageModule_PiMat_not_free`) |
| (6.1) | `exists_rank_one_factorization` |
| Proposition 6.2 | `dimension` (`exists_primes`, `two_le_ringKrullDim`, `not_isNoetherianRing`, `disjoint_span_Δ_powMulOneSub`) |
| §6.3 (namespace `Explicit`) | `Explicit.Astar`, `Explicit.φ`, `Explicit.span_u_v`, `Explicit.map_span_eq`, `Explicit.rel_prime`, `Explicit.Astar_isDomain`, `Explicit.equivAu`, `Explicit.equivAv`, `Explicit.Astar_smooth`, `Explicit.quotientEquiv`, `Explicit.u_prime`, `Explicit.Astar_ufd`, `Explicit.AstarSFD`, `Explicit.φ_injective`, `Explicit.Kstar`, `Explicit.isCompact_Kstar`, `Explicit.mapsTo_Kstar`, `Explicit.fiber_subsingleton`, `Explicit.fiber_one_zero`, `Explicit.isMonotoneSurjOn_Kstar`, `Explicit.Kstar_nonorientable`, `Explicit.principalization_extension_example` |
| §6.4: countable character; semihereditary rings | `HasCountableCharacter`, `hasCountableCharacter_iff`; `IsSemihereditary`, `IsBezout.isSemihereditary` |
| §6.4: Couchot's theorem (special case) | `hasSmithNormalForm_of_hasCountableCharacter` |
| Corollary 6.4 | `not_hasCountableCharacter` |
| §6.4: [CS, Lemma 5.1] and its `2 × 2` consequence | `cs_lemma_5_1`, `hasSmithNormalForm_of_countable_firstRow`, `uncountable_maximal_ideals` |
| §6.4: the example `C = ℚ[t, z₁, z₂, …]` | `ExampleC`, `maxIdealε`, `quotientMaxIdealε`, `exampleC_countable`, `exampleC_uncountable`, `exampleC_not_hasCountableCharacter` |
| Proposition 6.5 | `countable_reduction` |

## Deviations and formalization choices

**Conventions.**

* *Smooth finitely generated `ℚ`-domain* means `[CommRing A] [IsDomain A] [Algebra ℚ A]
  [Algebra.Smooth ℚ A]`; Mathlib's `Algebra.Smooth` includes finite presentation.
  `SmoothFactorialDomain` bundles such a ring with `UniqueFactorizationMonoid`.
* `A_𝔪` is `Localization.AtPrime 𝔪`, and `dim` is `ringKrullDim`.
* `Spec(A)(ℝ)` is `RealPt A`, the ring homomorphisms `A →+* ℝ`, with the coarsest topology for
  which the evaluations are continuous.
* A monotone surjection (`IsMonotoneSurjection`) is a continuous surjection with connected
  fibres. `IsMonotoneSurjOn q K' K` says that `q` maps `K'` into `K` and that the restriction
  `K' → K` is a monotone surjection.
* *A domain `R` containing `A₀`* is formalized by an injective ring homomorphism `ι : A₀ →+* R`,
  and `M` over `R` is `M.map ι`. The union `R = ⋃ Aₙ` of (5.1) is the direct limit
  (`Ring.DirectLimit`) of the injections `Aₙ ↪ Aₙ₊₁`, whose maps `Aₙ → R` are injective.
* Weight vectors are functions `ℕ → ℚ`. `e ⪯ e'` is `toLex e' ≤ toLex e`, and `e ≺ e'` is
  `e ⪯ e' ∧ e ≠ e'`.
* The paper's `𝓡₊` is `𝓡plus` (Lean identifiers cannot contain `₊`), and its `Π` is `PiMat`.
* Where the paper packs several claims into one statement (with "Consequently", "In particular",
  …), the Lean version usually has one lemma per claim. The table lists all of them, and several
  results also have a bundled version.

**Results quoted in the paper.**

* Theorem 3.3 is proved from the engine. Part (2) (smooth invariance) is proved when `B_𝔫` is a
  localization of a polynomial ring over `A_𝔪` (`IsLocalizationOfPolynomial`). The paper uses
  only this case in Lemmas 3.7 and 4.3. Its only other use is the stack-theoretic version in the
  proof of Theorem 3.6, which is proved differently here (next item).
* Theorem 3.6 is proved directly, not via the weighted blowup ([ATW, Theorem 6.2.1]) and smooth
  invariance on stacks. The engine (`Principalization/Drop.lean`, Brais's property (C)) combines
  three facts:
  * at the vertex of the Rees algebra, the weak transform has the invariant of `I`;
  * the invariant is upper semicontinuous on the smooth Rees algebra;
  * the `𝔾_m`-action `T ↦ μT` moves any closed point of `V(s) ∖ V(𝓡₊)` into a neighbourhood of
    the vertex.
* Couchot's theorem is proved only in the special case used for Corollary 6.4: over a Bézout
  domain of countable character, every `2 × 2` matrix has a Smith normal form. The proof goes
  through the `2 × 2` consequence of [CS, Lemma 5.1], which is proved by the iterative argument
  of Chen–Sheibani.

**Proofs and statements.**

* Proposition 4.6 is deduced from the stronger assertion `principalization_star`, as in the
  paper. That assertion is proved by well-founded induction on `(maxinv 𝔟, c(𝔟))` in
  `Γ_N × ℕ`, ordered lexicographically, using the divisorial step (Lemmas 4.1, 4.4) and the
  torsor step (Lemmas 4.2–4.5).
* Remark 4.7 is proved for the engine's version of the construction
  (`Principalization.principalizationExtension_strong`), an induction of the same shape with the
  same steps. The Lean statement says that some `A'`, `A → A'` and `K'` satisfy the conclusions
  of Proposition 4.6 together with properties (1) and (2) of the remark.
* Lemma 3.5(5): `𝓡/s𝓡 ≅ ⊕_{j ≥ 0} 𝓕_j/𝓕_{j+1}` is an isomorphism of `A`-modules
  (`quotientSEquiv`, induced by `f ↦ f T^j`). That the graded ring is a domain is
  `mul_not_mem_𝓕`: products of nonzero homogeneous elements are nonzero.
* Construction 5.1 uses Szudzik's pairing `Nat.pairEquiv` rather than Cantor's; the paper allows
  any bijection `⟨·,·⟩` with `i ≤ ⟨i, j⟩`.
* Proposition 6.1: *generated by two elements* is stated as a spanning family `Fin 2 → Π B²`.
* §6.3: the identification `𝓡* ≅ ℚ[t, u, v]` and the values of the invariant and of `d` for
  `(x - 1, y)` are explanatory and not formalized. The theorem
  `principalization_extension_example` states what the subsection proves: `(x - 1, y) A* = t A*`
  with `A*` a smooth finitely generated factorial `ℚ`-domain, `ℚ[x, y] → A*` injective, `K*`
  compact, and `K* → K₀` a monotone surjection. `A*[v⁻¹] ≅ ℚ[t, v, v⁻¹, u, r₀]` is obtained from
  `A*[u⁻¹] ≅ ℚ[t, u, u⁻¹, v, r₁]` through the involution `u ↔ v`, `r₀ ↔ r₁`.
* §6.4, the example `C`: the maximal ideals are indexed by `ε : ℕ → Bool`, with `ε k` standing
  for `ε_{k+1}`.

**Not formalized.**

* Remark 6.3, which relies on McGovern's theorem.
* Asides that no proof uses:
  * the literature discussion in §1 (Helmer, Kaplansky, Larsen–Lewis–Shores,
    Călugăreanu–Pop–Vasiu);
  * the description of `Spec J_B(c) → W` as an `E_c`-torsor in §3.2;
  * the comparison with the notation of [ATW, Brais] and the example `(y² - x³)` in §3.3;
  * the remark after Theorem 3.3 that the maximal locus is smooth of codimension `k`;
  * the remark after Lemma 4.5 about the case `k = 1`.

## License

MIT; see `LICENSE`.
