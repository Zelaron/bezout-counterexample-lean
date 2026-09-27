import BezoutCounterexample.Invariant

/-!
# Section 3.3: extended Rees algebras, the drop of the invariant, derivations

* **Notation 3.4** (`not:rees`): `ReesData A` bundles `A`, a nonzero proper ideal `I`, a component
  `V(𝔭)` of the maximal locus, and an integer `d ≥ 1` with `d eᵢ ∈ ℤ` (`e = maxinv I`). From it:
  `𝓕 j = F_{j/d}` (the global center, indexed by integers), the extended Rees algebra
  `𝓡 = ⊕ 𝓕_j T^j ⊆ A[T, T⁻¹]`, the exceptional element `s = T⁻¹`, the ideal
  `𝓡₊ = (𝓕_j T^j : j ≥ 1)` (`𝓡plus`), the weak transform `I_w = (f T^d : f ∈ I)`, and finite generating sets
  `G j` of `𝓕 j`.
* **Lemma 3.5** (`lem:rees`): parts (1)–(5); for (5), `quotientSEquiv` is the isomorphism
  `⊕_{j ≥ 0} 𝓕_j/𝓕_{j+1} ≅ 𝓡/s𝓡` (of `A`-modules, induced by `f ↦ f T^j`), `mul_not_mem_𝓕` says
  that products of nonzero homogeneous elements are nonzero, and `isDomain_quotient_s`, `prime_s`
  that `𝓡/s𝓡` is a domain.
* **Theorem 3.6** (`thm:drop`): `ReesData.drop`.
* **Lemma 3.7** (`lem:derivations`): `deriv_mem_maxCenter`, `ReesData.deriv_mem_𝓕` (part (1)) and
  `numNonzero_inv_add_le` (part (2)).

The proofs use the engine: `compFil` (the filtration `𝓕`), `ReesAlg`, `reesS`, `weakT`,
`reesPsi_ker` (the local presentation, quoted in the paper from Quek–Rydh), `rees_smooth`,
`span_s_isPrime`, `drop`, `deriv_mem_compF`, `length_le_of_derivations`.

The paper proves Theorem 3.6 by quoting the strict drop of the invariant on the weighted blowup
(Abramovich–Temkin–Włodarczyk, Theorem 6.2.1) and smooth invariance on stacks. The engine proves
it directly: the invariant of the weak transform at the vertex of the Rees algebra equals the old
invariant, the invariant is upper semicontinuous on the smooth Rees algebra, and the
`𝔾_m`-action `T ↦ μT` moves any point of `V(s) ∖ V(𝓡plus)` into a neighbourhood of the vertex.
-/

noncomputable section

namespace BezoutCounterexample

open IsLocalRing Principalization LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

/-! ## Auxiliary facts about invariants -/

omit [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] in
theorem Γ_nonneg {e : ℕ → ℚ} (he : e ∈ Γ) (i : ℕ) : 0 ≤ e i := by
  rcases he.1 i with h | ⟨a, ha, h⟩
  · rw [h]
  · rw [h]; positivity

/-- An invariant has finitely many nonzero entries. -/
theorem finite_support_inv {I : Ideal A} (hI : I ≠ ⊥) {𝔪 : Ideal A} [𝔪.IsMaximal]
    (hI𝔪 : I ≤ 𝔪) : {i | inv I 𝔪 i ≠ 0}.Finite := by
  obtain ⟨n, e, -, he⟩ := invAt_inv hI hI𝔪
  refine (Set.finite_lt_nat n).subset fun i hi => ?_
  by_contra hin
  apply hi
  rw [← he]
  simp only [ext0, dite_eq_right_iff]
  exact fun h => absurd h hin

theorem maxinv_mem_Γ {I : Ideal A} (hI : I ≠ ⊥) (hItop : I ≠ ⊤) : maxinv I ∈ Γ := by
  obtain ⟨⟨𝔪, h𝔪, hI𝔪, hinv⟩, -⟩ := maxinv_spec hI hItop
  rw [← hinv]; exact inv_mem_Γ hI hI𝔪

theorem finite_support_maxinv {I : Ideal A} (hI : I ≠ ⊥) (hItop : I ≠ ⊤) :
    {i | maxinv I i ≠ 0}.Finite := by
  obtain ⟨⟨𝔪, h𝔪, hI𝔪, hinv⟩, -⟩ := maxinv_spec hI hItop
  rw [← hinv]; exact finite_support_inv hI hI𝔪

omit [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] in
/-- For `e ∈ Γ` with finitely many nonzero entries, `eᵢ ≠ 0` exactly for `i < k`, `k` the number
of nonzero entries. -/
theorem ne_zero_iff_lt_numNonzero {e : ℕ → ℚ} (he : e ∈ Γ) (hfin : {i | e i ≠ 0}.Finite)
    (i : ℕ) : e i ≠ 0 ↔ i < numNonzero e := by
  -- the support is downward closed
  have hdown : ∀ j l, j ≤ l → e l ≠ 0 → e j ≠ 0 := by
    intro j l hjl hl hj
    apply hl
    induction l, hjl using Nat.le_induction with
    | base => exact hj
    | succ l _ ih => exact he.2 l (ih (fun h => hl (he.2 l h)))
  -- a finite downward closed set of naturals is an initial segment
  have hseg : {i | e i ≠ 0} = ↑(Finset.range (numNonzero e)) := by
    by_cases hne : {i | e i ≠ 0}.Nonempty
    · obtain ⟨M, hM, hmax⟩ := Set.exists_max_image _ id hfin hne
      have hS : {i | e i ≠ 0} = ↑(Finset.range (M + 1)) := by
        ext j
        simp only [Set.mem_ofPred_eq, Finset.coe_range, Set.mem_Iio]
        constructor
        · intro hj
          have := hmax j hj
          simp only [id] at this
          omega
        · intro hj
          exact hdown j M (by omega) hM
      have hcard : numNonzero e = M + 1 := by
        unfold numNonzero; rw [hS, Set.ncard_coe_finset, Finset.card_range]
      rw [hcard, hS]
    · have h0 : {i | e i ≠ 0} = ∅ := Set.not_nonempty_iff_eq_empty.1 hne
      have hcard : numNonzero e = 0 := by unfold numNonzero; rw [h0, Set.ncard_empty]
      rw [hcard, h0]; simp
  have := congrArg (i ∈ ·) hseg
  simpa using this

theorem maxLocusIdeal_eq_locusIdeal {I : Ideal A} (hI : I ≠ ⊥) :
    maxLocusIdeal I = locusIdeal I (maxinv I) := by
  unfold maxLocusIdeal locusIdeal maxLocus
  congr 1
  ext 𝔪
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h𝔪, hI𝔪, hinv⟩
    exact ⟨h𝔪, hI𝔪, hinv ▸ invAt_inv hI hI𝔪⟩
  · rintro ⟨h𝔪, hI𝔪, hv⟩
    exact ⟨h𝔪, hI𝔪, inv_eq_of_invAt hI hI𝔪 hv⟩

theorem le_of_mem_components {I : Ideal A} (hI : I ≠ ⊥) (hItop : I ≠ ⊤) {𝔭 : Ideal A}
    (h𝔭 : 𝔭 ∈ components I) : I ≤ 𝔭 :=
  ((theorem_3_3_3 hI hItop).2.1 𝔭 h𝔭).2

/-! ## Notation 3.4 -/

/-- **Notation 3.4** (`not:rees`). `A` is a smooth finitely generated `ℚ`-domain, `I ⊊ A` is a
nonzero ideal, `V(𝔭)` is a component of the maximal locus of `I`, and `d ≥ 1` is an integer with
`d eᵢ ∈ ℤ` for all `i`, where `e = maxinv(I)`. -/
structure ReesData (A : Type) [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] where
  /-- The ideal `I`. -/
  I : Ideal A
  ne_bot : I ≠ ⊥
  ne_top : I ≠ ⊤
  /-- The component `V(𝔭)` of the maximal locus. -/
  𝔭 : Ideal A
  mem_components : 𝔭 ∈ components I
  /-- The common denominator `d`. -/
  d : ℕ
  one_le_d : 1 ≤ d
  d_mul : ∀ i, ∃ w : ℤ, (d : ℚ) * maxinv I i = w

namespace ReesData

variable (S : ReesData A)

/-- `e = maxinv(I)`. -/
def e : ℕ → ℚ := maxinv S.I

/-- `k`, the number of nonzero entries of `e`. -/
def k : ℕ := numNonzero S.e

/-- The engine form of maximality of `e`. -/
theorem hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], S.I ≤ 𝔪 → ∀ v, InvAt S.I 𝔪 v →
    toLex (maxinv S.I) ≤ toLex v := by
  intro 𝔪 _ hI𝔪 v hv
  rw [← inv_eq_of_invAt S.ne_bot hI𝔪 hv]
  exact (maxinv_spec S.ne_bot S.ne_top).2 𝔪 hI𝔪

/-- The engine form of `𝔭 ∈ components I`. -/
theorem h𝔭 : S.𝔭 ∈ (locusIdeal S.I (maxinv S.I)).minimalPrimes := by
  rw [← maxLocusIdeal_eq_locusIdeal S.ne_bot]; exact S.mem_components

theorem d_pos : 0 < S.d := S.one_le_d

theorem hw : ∀ i, ∃ w : ℕ, (w : ℚ) = S.d * maxinv S.I i := by
  intro i
  obtain ⟨z, hz⟩ := S.d_mul i
  have h0 : (0 : ℚ) ≤ z :=
    hz ▸ mul_nonneg (Nat.cast_nonneg _) (Γ_nonneg (maxinv_mem_Γ S.ne_bot S.ne_top) i)
  have h0' : (0 : ℤ) ≤ z := by exact_mod_cast h0
  refine ⟨z.toNat, ?_⟩
  rw [hz]
  exact_mod_cast Int.toNat_of_nonneg h0'

/-- The global center indexed by integers: `𝓕 j = F_{j/d}`. -/
def 𝓕 (j : ℤ) : Ideal A := globalCenter S.I S.𝔭 ((j : ℚ) / S.d)

/-- The filtration `(𝓕 j)` as an engine filtration. -/
abbrev fil : WFil A := compFil S.ne_bot S.hmax S.h𝔭 S.d

theorem fil_F (j : ℤ) : S.fil.F j = S.𝓕 j := by
  show compF S.I S.𝔭 ((j : ℚ) / S.d) = globalCenter S.I S.𝔭 ((j : ℚ) / S.d)
  have hI𝔭 := le_of_mem_components S.ne_bot S.ne_top S.mem_components
  ext f
  rw [mem_compF, mem_globalCenter]
  constructor
  · intro h 𝔪 _ h𝔭𝔪
    rw [maxCenter_eq_cRF S.ne_bot (hI𝔭.trans h𝔭𝔪)]
    exact h 𝔪 h𝔭𝔪
  · intro h 𝔪 _ h𝔭𝔪
    rw [← maxCenter_eq_cRF S.ne_bot (hI𝔭.trans h𝔭𝔪)]
    exact h 𝔪 h𝔭𝔪

/-- The extended Rees algebra `𝓡 = ⊕_{j ∈ ℤ} 𝓕_j T^j ⊆ A[T, T⁻¹]` of the weighted center along
`V(𝔭)`. -/
abbrev 𝓡 : Subalgebra A A[T;T⁻¹] := ReesAlg S.fil

theorem mem_𝓡 (p : A[T;T⁻¹]) : p ∈ S.𝓡 ↔ ∀ j, p.coeff j ∈ S.𝓕 j := by
  show (∀ j, p.coeff j ∈ S.fil.F j) ↔ _
  simp only [S.fil_F]

theorem C_mul_T_mem {j : ℤ} {f : A} (hf : f ∈ S.𝓕 j) : C f * T j ∈ S.𝓡 :=
  C_mul_T_mem_ReesAlg (Φ := S.fil) (by rw [S.fil_F]; exact hf)

/-- The element `f T^j ∈ 𝓡` for `f ∈ 𝓕 j`. -/
def mono (j : ℤ) (f : A) (hf : f ∈ S.𝓕 j) : S.𝓡 := ⟨C f * T j, S.C_mul_T_mem hf⟩

/-- The exceptional element `s = T⁻¹ ∈ 𝓡`. -/
def s : S.𝓡 := reesS S.fil (fun _j hj => compFil_F_nonpos S.ne_bot S.hmax S.h𝔭 S.d hj)

@[simp] lemma s_coe : (S.s : A[T;T⁻¹]) = T (-1) := rfl

/-- `𝓡₊ = (𝓕_j T^j : j ≥ 1) 𝓡`. -/
def 𝓡plus : Ideal S.𝓡 :=
  Ideal.span {r : S.𝓡 | ∃ (j : ℤ) (f : A), 1 ≤ j ∧ f ∈ S.𝓕 j ∧ (r : A[T;T⁻¹]) = C f * T j}

theorem I_le_fil : S.I ≤ S.fil.F S.d := I_le_compFil S.ne_bot S.hmax S.h𝔭 S.d_pos

/-- The weak transform `I_w = (f T^d : f ∈ I) 𝓡` of `I`. -/
def Iw : Ideal S.𝓡 := weakT S.fil S.I S.d S.I_le_fil

/-- Finite generating sets `G j` of `𝓕 j`. -/
def G (j : ℤ) : Finset A := gensF S.ne_bot S.hmax S.h𝔭 S.d j

theorem span_G (j : ℤ) : Ideal.span (S.G j : Set A) = S.𝓕 j := by
  rw [G, span_gensF]; exact S.fil_F j

instance : Algebra.Smooth ℚ S.𝓡 := rees_smooth S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw

/-! ## Lemma 3.5 -/

/-- **Lemma 3.5(1)**: `𝓕_j = A` for `j ≤ 0`. -/
theorem 𝓕_of_nonpos {j : ℤ} (hj : j ≤ 0) : S.𝓕 j = ⊤ := by
  rw [← S.fil_F]; exact compFil_F_nonpos S.ne_bot S.hmax S.h𝔭 S.d hj

/-- **Lemma 3.5(1)**: `𝓕₁ = 𝔭`. -/
theorem 𝓕_one : S.𝓕 1 = S.𝔭 := by
  rw [← S.fil_F, fil, compFil_F, show ((1 : ℤ) : ℚ) / S.d = 1 / S.d by push_cast; ring]
  exact compF_one_div S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw

/-- **Lemma 3.5(1)**: `𝔭^j ⊆ 𝓕_j` for `j ≥ 0`. -/
theorem pow_le_𝓕 (j : ℕ) : S.𝔭 ^ j ≤ S.𝓕 j := by
  rw [← S.fil_F, fil, compFil_F, show ((j : ℤ) : ℚ) = (j : ℚ) by push_cast; ring]
  exact pow_le_compF S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw j

/-- **Lemma 3.5(1)**: `I ⊆ 𝓕_d` (admissibility). -/
theorem I_le_𝓕 : S.I ≤ S.𝓕 S.d := by
  rw [← S.fil_F]; exact S.I_le_fil

/-- **Lemma 3.5(1)**: `I 𝓡 = s^d I_w`. -/
theorem map_I_eq : S.I.map (algebraMap A S.𝓡) = Ideal.span {S.s ^ S.d} * S.Iw :=
  map_eq_weakT S.fil _ S.I S.d S.I_le_fil

/-- **Lemma 3.5(1)**: `𝔭 = 𝓕₁ ⊆ s 𝓡`. -/
theorem map_𝔭_le : S.𝔭.map (algebraMap A S.𝓡) ≤ Ideal.span {S.s} := by
  rw [Ideal.map_le_iff_le_comap]
  intro g hg
  have hg1 : g ∈ S.𝓕 1 := by rw [S.𝓕_one]; exact hg
  rw [Ideal.mem_comap, Ideal.mem_span_singleton']
  refine ⟨S.mono 1 g hg1, Subtype.ext ?_⟩
  show C g * T 1 * T (-1) = algebraMap A A[T;T⁻¹] g
  rw [mul_assoc, ← T_add, add_neg_cancel, T_zero, mul_one, LaurentPolynomial.C_eq_algebraMap]

/-- **Lemma 3.5(2)**: `𝓕_j = ∑_{q=1}^d 𝓕_q 𝓕_{j-q}` for `j > d`. -/
theorem 𝓕_eq_sum {j : ℤ} (hj : (S.d : ℤ) < j) :
    S.𝓕 j = ⨆ q ∈ Finset.Icc (1 : ℤ) S.d, S.𝓕 q * S.𝓕 (j - q) := by
  simp only [← S.fil_F]
  refine le_antisymm (compFil_le_iSup S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw hj)
    (iSup₂_le fun q _ => ?_)
  have := S.fil.mul_le q (j - q)
  rwa [add_sub_cancel] at this

/-- The generators `s` and `g T^j` (`g ∈ G_j`, `1 ≤ j ≤ d`) of `𝓡`. -/
def gens : Set A[T;T⁻¹] :=
  {T (-1)} ∪ ⋃ j ∈ Finset.Icc (1 : ℤ) S.d, (fun g => C g * T j) '' (S.G j : Set A)

/-- **Lemma 3.5(2)**: `𝓡 = A[s, g T^j : g ∈ G_j, 1 ≤ j ≤ d]`. -/
theorem 𝓡_eq_adjoin : S.𝓡 = Algebra.adjoin A S.gens :=
  reesAlg_eq_adjoin S.ne_bot S.hmax S.h𝔭 S.d S.d_pos S.hw

/-- **Lemma 3.5(2)**: the elements `g T^j`, `g ∈ G_j`, `1 ≤ j ≤ d`, generate `𝓡plus`. -/
theorem 𝓡plus_eq_span : S.𝓡plus = Ideal.span {r : S.𝓡 | ∃ j ∈ Finset.Icc (1 : ℤ) S.d, ∃ g ∈ S.G j,
    (r : A[T;T⁻¹]) = C g * T j} := by
  set J := Ideal.span {r : S.𝓡 | ∃ j ∈ Finset.Icc (1 : ℤ) S.d, ∃ g ∈ S.G j,
    (r : A[T;T⁻¹]) = C g * T j}
  -- sums and multiples of elements `f T^j ∈ J`
  have hadd : ∀ {j : ℤ} {f₁ f₂ : A} (h₁ : f₁ ∈ S.𝓕 j) (h₂ : f₂ ∈ S.𝓕 j),
      S.mono j f₁ h₁ ∈ J → S.mono j f₂ h₂ ∈ J → S.mono j (f₁ + f₂) (add_mem h₁ h₂) ∈ J := by
    intro j f₁ f₂ h₁ h₂ hJ₁ hJ₂
    have : S.mono j (f₁ + f₂) (add_mem h₁ h₂) = S.mono j f₁ h₁ + S.mono j f₂ h₂ :=
      Subtype.ext (by simp [mono, add_mul])
    rw [this]; exact add_mem hJ₁ hJ₂
  have hzero : ∀ j : ℤ, S.mono j 0 (zero_mem _) ∈ J := fun j => by
    have : S.mono j 0 (zero_mem _) = 0 := Subtype.ext (by simp [mono])
    rw [this]; exact zero_mem _
  apply le_antisymm
  · rw [𝓡plus, Ideal.span_le]
    rintro r ⟨j, f, hj1, hf, hr⟩
    have hr' : r = S.mono j f hf := Subtype.ext hr
    rw [hr']
    -- every `f T^j` with `j ≥ 1` and `f ∈ 𝓕_j` lies in `J`, by strong induction on `j`
    suffices H : ∀ n : ℕ, ∀ j : ℤ, 1 ≤ j → j ≤ n → ∀ f (hf : f ∈ S.𝓕 j), S.mono j f hf ∈ J from
      H j.toNat j hj1 (Int.self_le_toNat j) f hf
    intro n
    induction n with
    | zero => intro j hj1 hjn; omega
    | succ n ih =>
      intro j hj1 hjn f hf
      by_cases hjd : j ≤ S.d
      · -- `f` is a combination of the generators `G_j`
        have hfG : f ∈ Ideal.span (S.G j : Set A) := by rw [S.span_G]; exact hf
        induction hfG using Submodule.span_induction with
        | mem g hg =>
          exact Ideal.subset_span ⟨j, Finset.mem_Icc.2 ⟨hj1, hjd⟩, g, hg, rfl⟩
        | zero => exact hzero j
        | add f₁ f₂ h₁ h₂ ih₁ ih₂ =>
          have h₁' : f₁ ∈ S.𝓕 j := by rw [← S.span_G]; exact h₁
          have h₂' : f₂ ∈ S.𝓕 j := by rw [← S.span_G]; exact h₂
          exact hadd h₁' h₂' (ih₁ h₁') (ih₂ h₂')
        | smul a f₁ h₁ ih₁ =>
          replace h₁ : f₁ ∈ S.𝓕 j := by rw [← S.span_G]; exact h₁
          have : S.mono j (a • f₁) hf = algebraMap A S.𝓡 a * S.mono j f₁ h₁ :=
            Subtype.ext (by
              simp only [mono, smul_eq_mul, map_mul, Subalgebra.coe_mul, Subalgebra.coe_algebraMap,
                LaurentPolynomial.C_eq_algebraMap]
              ring)
          rw [this]; exact Ideal.mul_mem_left _ _ (ih₁ h₁)
      · -- `j > d`: `𝓕_j = ∑_q 𝓕_q 𝓕_{j-q}`, and `f_q T^q ∈ J` for `1 ≤ q ≤ d` by induction
        push Not at hjd
        have hmemj : ∀ {q : ℤ} {a b : A}, a ∈ S.𝓕 q → b ∈ S.𝓕 (j - q) → a * b ∈ S.𝓕 j := by
          intro q a b ha hb
          have := S.fil.mul_le q (j - q) (Ideal.mul_mem_mul (by rw [S.fil_F]; exact ha)
            (by rw [S.fil_F]; exact hb))
          rwa [add_sub_cancel, S.fil_F] at this
        have key : ∀ g, g ∈ ⨆ q ∈ Finset.Icc (1 : ℤ) S.d, S.𝓕 q * S.𝓕 (j - q) →
            g ∈ S.𝓕 j ∧ ∀ hg : g ∈ S.𝓕 j, S.mono j g hg ∈ J := by
          intro g hg
          refine Submodule.iSup_induction _ (motive := fun g => g ∈ S.𝓕 j ∧
            ∀ hg : g ∈ S.𝓕 j, S.mono j g hg ∈ J) hg (fun q g hgq => ?_) ⟨zero_mem _, fun _ => hzero j⟩
            (fun g₁ g₂ ih₁ ih₂ => ⟨add_mem ih₁.1 ih₂.1, fun _ => hadd ih₁.1 ih₂.1 (ih₁.2 _)
              (ih₂.2 _)⟩)
          refine Submodule.iSup_induction _ (motive := fun g => g ∈ S.𝓕 j ∧
            ∀ hg : g ∈ S.𝓕 j, S.mono j g hg ∈ J) hgq (fun hq g hgq' => ?_) ⟨zero_mem _, fun _ => hzero j⟩
            (fun g₁ g₂ ih₁ ih₂ => ⟨add_mem ih₁.1 ih₂.1, fun _ => hadd ih₁.1 ih₂.1 (ih₁.2 _)
              (ih₂.2 _)⟩)
          have hq' := Finset.mem_Icc.1 hq
          refine Submodule.mul_induction_on (C := fun g => g ∈ S.𝓕 j ∧
            ∀ hg : g ∈ S.𝓕 j, S.mono j g hg ∈ J) hgq' (fun a ha b hb => ⟨hmemj ha hb, fun hab => ?_⟩)
            (fun g₁ g₂ ih₁ ih₂ => ⟨add_mem ih₁.1 ih₂.1, fun _ => hadd ih₁.1 ih₂.1 (ih₁.2 _)
              (ih₂.2 _)⟩)
          have hmul : S.mono j (a * b) hab = S.mono q a ha * S.mono (j - q) b hb :=
            Subtype.ext (by
              simp only [mono, Subalgebra.coe_mul]
              conv_lhs => rw [show j = q + (j - q) by ring]
              rw [map_mul, T_add]; ring)
          rw [hmul]
          exact Ideal.mul_mem_right _ _ (ih q hq'.1 (by omega) a ha)
        exact (key f (by rw [← S.𝓕_eq_sum hjd]; exact hf)).2 hf
  · rw [Ideal.span_le]
    rintro r ⟨j, hj, g, hg, hr⟩
    exact Ideal.subset_span ⟨j, g, (Finset.mem_Icc.1 hj).1,
      by rw [← S.span_G]; exact Ideal.subset_span hg, hr⟩

/-- **Lemma 3.5(3)**: `𝓡[1/s] = A[T, T⁻¹]`. -/
theorem isLocalization_away_s : IsLocalization.Away S.s A[T;T⁻¹] :=
  Principalization.isLocalization_away_s S.fil _

/-- **Lemma 3.5(4)**: the formation of `𝓡` commutes with localization: `𝓡 ⊗_A A_𝔪` is the extended
Rees algebra of the filtration `(F_{j/d}(𝔪))_j`, i.e. of `(𝓕_j A_𝔪)_j`. -/
theorem isLocalization_rees (𝔪 : Ideal A) [𝔪.IsMaximal] :
    @IsLocalization _ _ (𝔪.primeCompl.map (algebraMap A S.𝓡))
      (ReesAlg (S.fil.loc (Localization.AtPrime 𝔪))) _
      (reesMap S.fil (Localization.AtPrime 𝔪)).toAlgebra :=
  reesMap_isLocalization S.fil _ 𝔪.primeCompl (Ideal.primeCompl_le_nonZeroDivisors 𝔪)

/-- The localized filtration is the maximal center: `𝓕_j A_𝔪 = F_{j/d}(𝔪)` for `𝔪 ⊇ 𝔭`. -/
theorem fil_loc_F (𝔪 : Ideal A) [𝔪.IsMaximal] (h𝔭𝔪 : S.𝔭 ≤ 𝔪) (j : ℤ) :
    (S.fil.loc (Localization.AtPrime 𝔪)).F j = maxCenter S.I 𝔪 ((j : ℚ) / S.d) := by
  rw [maxCenter_eq_cRF S.ne_bot
    ((le_of_mem_components S.ne_bot S.ne_top S.mem_components).trans h𝔭𝔪)]
  exact compFil_loc_F S.ne_bot S.hmax S.h𝔭 S.d 𝔪 h𝔭𝔪 j

/-- The integer weights `wᵢ = d eᵢ`. -/
def w (i : ℕ) : ℕ := ((S.d : ℚ) * S.e i).num.toNat

theorem w_spec (i : ℕ) : (S.w i : ℚ) = S.d * S.e i := by
  obtain ⟨z, hz⟩ := S.d_mul i
  have h0 : (0 : ℚ) ≤ z :=
    hz ▸ mul_nonneg (Nat.cast_nonneg _) (Γ_nonneg (maxinv_mem_Γ S.ne_bot S.ne_top) i)
  have h0' : (0 : ℤ) ≤ z := by exact_mod_cast h0
  have : S.w i = z.toNat := by simp only [w, e, hz, Rat.num_intCast]
  rw [this, e, hz]
  exact_mod_cast Int.toNat_of_nonneg h0'

/-- **Lemma 3.5(4)**: let `𝔪 ⊇ 𝔭` be maximal and let `x` be as in Theorem 3.3(3). Then
`uᵢ ↦ xᵢ T^{wᵢ}` induces an isomorphism
`A_𝔪[s, u₁, …, u_k]/(xᵢ - s^{wᵢ} uᵢ | 1 ≤ i ≤ k) ≅ 𝓡 ⊗_A A_𝔪`, where `𝓡 ⊗_A A_𝔪` is the extended
Rees algebra of the localized filtration (`isLocalization_rees`). -/
theorem rees_presentation (𝔪 : Ideal A) [𝔪.IsMaximal] (h𝔭𝔪 : S.𝔭 ≤ 𝔪) (J : MarkedCenter 𝔪)
    (hJw : J.weights = maxinv S.I) (hJ : J.IsAdmissible S.I)
    (_hJ𝔭 : S.𝔭.map (algebraMap A (Localization.AtPrime 𝔪)) =
      Ideal.span (J.x '' {i | (i : ℕ) < S.k})) (hkn : S.k ≤ J.n) :
    ∃ φ : (MvPolynomial (Option (Fin S.k)) (Localization.AtPrime 𝔪) ⧸
        Ideal.span (Set.range fun i : Fin S.k =>
          MvPolynomial.C (J.x (Fin.castLE hkn i)) -
            MvPolynomial.X none ^ S.w i * MvPolynomial.X (some i))) ≃ₐ[Localization.AtPrime 𝔪]
        ReesAlg (S.fil.loc (Localization.AtPrime 𝔪)),
      ((φ (Ideal.Quotient.mk _ (MvPolynomial.X none)) : (Localization.AtPrime 𝔪)[T;T⁻¹]) =
        T (-1)) ∧
      ∀ i : Fin S.k, ((φ (Ideal.Quotient.mk _ (MvPolynomial.X (some i))) :
        (Localization.AtPrime 𝔪)[T;T⁻¹]) = C (J.x (Fin.castLE hkn i)) * T (S.w i)) := by
  classical
  -- a centred chart with coordinates `x`
  obtain ⟨c, hcx, hc⟩ := J.isRegular.exists_chart
  have hI𝔪 : S.I ≤ 𝔪 := (le_of_mem_components S.ne_bot S.ne_top S.mem_components).trans h𝔭𝔪
  have hinv : inv S.I 𝔪 = maxinv S.I :=
    ((theorem_3_3_3 S.ne_bot S.ne_top).2.2.2.1 𝔪 hI𝔪).2 ⟨S.𝔭, S.mem_components, h𝔭𝔪⟩
  have hJe : ∀ i : Fin J.n, J.e i = S.e i := fun i => by
    have := congrFun hJw i
    simpa [MarkedCenter.weights, ReesData.e] using this
  -- the localized filtration is the filtration of the marked center `(x, e)`
  have hF : ∀ j, (S.fil.loc (Localization.AtPrime 𝔪)).F j = chartFil c J.e S.d j := by
    intro j
    rw [S.fil_loc_F 𝔪 h𝔭𝔪 j, ← J.F_eq_maxCenter S.ne_bot hI𝔪 hJ (hJw.trans hinv.symm),
      J.F_eq_RF c hcx]
    rfl
  set wn : Fin J.n → ℕ := fun i => S.w i
  have hw : ∀ i, (wn i : ℚ) = S.d * J.e i := fun i => by
    simp only [wn]; rw [S.w_spec, hJe]
  have hsupp : ∀ i : Fin J.n, J.e i ≠ 0 ↔ (i : ℕ) < S.k := fun i => by
    rw [hJe]
    exact ne_zero_iff_lt_numNonzero (maxinv_mem_Γ S.ne_bot S.ne_top)
      (finite_support_maxinv S.ne_bot S.ne_top) i
  have hsurj := reesPsi_surjective c hF J.nonneg S.d_pos hw hkn hsupp
  have hrel : Ideal.span (Set.range fun i : Fin S.k =>
      MvPolynomial.C (J.x (Fin.castLE hkn i)) -
        MvPolynomial.X none ^ S.w i * MvPolynomial.X (some i)) =
      RingHom.ker (reesPsi c hF J.nonneg S.d_pos hw hkn) := by
    rw [reesPsi_ker c hc hF J.nonneg S.d_pos hw hkn hsupp]
    congr 2
    funext i
    simp only [reesRel, hcx]
    rfl
  refine ⟨(Ideal.quotientEquivAlgOfEq (Localization.AtPrime 𝔪) hrel).trans
    (Ideal.quotientKerAlgEquivOfSurjective hsurj), ?_, fun i => ?_⟩
  · rw [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
      Ideal.quotientKerAlgEquivOfSurjective_mk]
    simp only [reesPsi, MvPolynomial.aeval_X, reesGen, Option.elim]
    exact reesX_last c hF J.nonneg S.d_pos hw
  · rw [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
      Ideal.quotientKerAlgEquivOfSurjective_mk]
    simp only [reesPsi, MvPolynomial.aeval_X, reesGen, Option.elim]
    rw [reesX_castSucc c hF J.nonneg S.d_pos hw, hcx]
    rfl

/-- **Lemma 3.5(4)**: if `𝔪 ⊉ 𝔭`, then `𝓡 ⊗_A A_𝔪 = A_𝔪[T, T⁻¹]`. -/
theorem rees_loc_eq_top (𝔪 : Ideal A) [𝔪.IsMaximal] (h𝔭𝔪 : ¬ S.𝔭 ≤ 𝔪) :
    ReesAlg (S.fil.loc (Localization.AtPrime 𝔪)) = ⊤ := by
  rw [eq_top_iff]
  intro p _ j
  have : (S.fil.loc (Localization.AtPrime 𝔪)).F j = ⊤ :=
    compF_map_of_not_le S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw 𝔪 h𝔭𝔪 _
  rw [this]; trivial

/-- **Lemma 3.5(4)**: `𝓡` is a smooth finitely generated `ℚ`-domain. -/
theorem rees_smooth_domain : IsDomain S.𝓡 ∧ Algebra.Smooth ℚ S.𝓡 :=
  ⟨inferInstance, inferInstance⟩

/-- **Lemma 3.5(5)**: `s 𝓡 ∩ 𝓕_j T^j = 𝓕_{j+1} T^j`, so that the degree-`j` part of `𝓡/s𝓡` is
`𝓕_j/𝓕_{j+1}`. -/
theorem mono_mem_span_s_iff {j : ℤ} {f : A} (hf : f ∈ S.𝓕 j) :
    S.mono j f hf ∈ Ideal.span {S.s} ↔ f ∈ S.𝓕 (j + 1) := by
  rw [s]
  refine (mem_span_s_iff S.fil _ _).trans ?_
  constructor
  · intro h
    have := h j
    simp only [mono, coeff_C_mul_T, ite_true] at this
    rwa [S.fil_F] at this
  · intro h i
    simp only [mono, coeff_C_mul_T]
    split_ifs with hij
    · subst hij; rw [S.fil_F]; exact h
    · exact zero_mem _

/-- The graded piece `𝓕_j/𝓕_{j+1}` of the associated graded ring, as an `A`-module (`j ≥ 0`). -/
abbrev grPiece (j : ℕ) : Type := ↥(S.𝓕 j) ⧸ Submodule.comap (S.𝓕 j).subtype (S.𝓕 (j + 1))

/-- `f ↦ f T^j`, as an `A`-linear map `𝓕_j → 𝓡`. -/
def monoLin (j : ℤ) : ↥(S.𝓕 j) →ₗ[A] S.𝓡 where
  toFun f := S.mono j f f.2
  map_add' f g := Subtype.ext (by simp [mono, add_mul])
  map_smul' a f := Subtype.ext (by
    show C (a * (f : A)) * T j = a • (C (f : A) * T j)
    rw [Algebra.smul_def, map_mul, LaurentPolynomial.C_eq_algebraMap,
      LaurentPolynomial.C_eq_algebraMap]
    ring)

@[simp] lemma monoLin_apply (j : ℤ) (f : ↥(S.𝓕 j)) : S.monoLin j f = S.mono j f f.2 := rfl

/-- The class of `f T^j` in `𝓡/s𝓡`. -/
def grToQuot (j : ℕ) : S.grPiece j →ₗ[A] (S.𝓡 ⧸ Ideal.span {S.s}) :=
  Submodule.liftQ _ ((Ideal.Quotient.mkₐ A (Ideal.span {S.s})).toLinearMap ∘ₗ S.monoLin j)
    (fun f hf => by
      simp only [Submodule.mem_comap, Submodule.coe_subtype] at hf
      rw [LinearMap.mem_ker, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, monoLin_apply]
      exact (S.mono_mem_span_s_iff f.2).2 (by exact_mod_cast hf))

lemma grToQuot_mk (j : ℕ) (f : ↥(S.𝓕 j)) :
    S.grToQuot j (Submodule.Quotient.mk f) = Ideal.Quotient.mk _ (S.mono j f f.2) := rfl

/-- The map `⊕_{j ≥ 0} 𝓕_j/𝓕_{j+1} → 𝓡/s𝓡`. -/
def gradedToQuot : (DirectSum ℕ S.grPiece) →ₗ[A] (S.𝓡 ⧸ Ideal.span {S.s}) :=
  DirectSum.toModule A ℕ _ S.grToQuot

/-- Every element of `𝓡` is a finite sum of homogeneous elements `f T^j`. -/
lemma mem_span_mono (r : S.𝓡) :
    r ∈ Submodule.span A {x : S.𝓡 | ∃ (j : ℤ) (f : A) (hf : f ∈ S.𝓕 j), x = S.mono j f hf} := by
  classical
  have hr : (r : A[T;T⁻¹]) = ∑ j ∈ (r : A[T;T⁻¹]).coeff.support,
      C ((r : A[T;T⁻¹]).coeff j) * T j := by
    conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single (r : A[T;T⁻¹])]
    rw [Finsupp.sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [single_eq_C_mul_T]
  have hr' : r = ∑ j ∈ (r : A[T;T⁻¹]).coeff.support,
      S.mono j ((r : A[T;T⁻¹]).coeff j) ((S.mem_𝓡 _).1 r.2 j) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact hr
  rw [hr']
  exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨j, _, _, rfl⟩

theorem gradedToQuot_surjective : Function.Surjective S.gradedToQuot := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro q -
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hr := S.mem_span_mono r
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, f, hf, rfl⟩ := hx
    by_cases hj : 0 ≤ j
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
      refine ⟨DirectSum.of S.grPiece n (Submodule.Quotient.mk ⟨f, hf⟩), ?_⟩
      rw [gradedToQuot, ← DirectSum.lof_eq_of A, DirectSum.toModule_lof, grToQuot_mk]
    · -- in negative degrees, `f T^j ∈ s𝓡`
      refine ⟨0, ?_⟩
      rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
      refine (S.mono_mem_span_s_iff hf).2 ?_
      rw [S.𝓕_of_nonpos (by omega)]; trivial
  | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
  | smul a x _ hx =>
    obtain ⟨b, hb⟩ := hx
    refine ⟨a • b, ?_⟩
    rw [map_smul, hb]
    rfl

theorem gradedToQuot_injective : Function.Injective S.gradedToQuot := by
  classical
  rw [injective_iff_map_eq_zero]
  intro x hx
  -- choose representatives of the components of `x`
  choose f hf using fun j => Submodule.Quotient.mk_surjective _ (x j)
  have hxsum : x = ∑ j ∈ x.support, DirectSum.of S.grPiece j (Submodule.Quotient.mk (f j)) := by
    conv_lhs => rw [← DirectSum.sum_support_of x]
    exact Finset.sum_congr rfl fun j _ => by rw [hf j]
  have hx' : Ideal.Quotient.mk (Ideal.span {S.s})
      (∑ j ∈ x.support, S.mono j (f j : A) (f j).2) = 0 := by
    rw [← hx]
    conv_rhs => rw [hxsum]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [gradedToQuot, ← DirectSum.lof_eq_of A, DirectSum.toModule_lof, grToQuot_mk]
  rw [Ideal.Quotient.eq_zero_iff_mem, s] at hx'
  -- all coefficients lie one step deeper
  have hcoef := (mem_span_s_iff S.fil _ _).1 hx'
  have hall : ∀ j ∈ x.support, ((f j : ↥(S.𝓕 j)) : A) ∈ S.𝓕 (j + 1) := by
    intro j hj
    have := hcoef j
    rw [AddSubmonoidClass.coe_finsetSum, laurent_coeff_sum] at this
    rw [Finset.sum_eq_single_of_mem j hj] at this
    · simpa [mono, coeff_C_mul_T, S.fil_F] using this
    · intro i _ hij
      simp [mono, coeff_C_mul_T, Nat.cast_inj, Ne.symm hij]
  ext j
  by_cases hj : j ∈ x.support
  · rw [← hf j, DirectSum.zero_apply, Submodule.Quotient.mk_eq_zero]
    simp only [Submodule.mem_comap, Submodule.coe_subtype]
    exact_mod_cast hall j hj
  · rw [DFinsupp.notMem_support_iff.1 hj, DirectSum.zero_apply]

/-- **Lemma 3.5(5)**: `𝓡/s𝓡 ≅ ⊕_{j ≥ 0} 𝓕_j/𝓕_{j+1}`, induced by `f ↦ f T^j` (as `A`-modules; the
ring structure of `𝓡/s𝓡` corresponds to the multiplication of initial forms). -/
def quotientSEquiv : (DirectSum ℕ S.grPiece) ≃ₗ[A] (S.𝓡 ⧸ Ideal.span {S.s}) :=
  LinearEquiv.ofBijective S.gradedToQuot ⟨S.gradedToQuot_injective, S.gradedToQuot_surjective⟩

/-- **Lemma 3.5(5)**: `⊕_{j ≥ 0} 𝓕_j/𝓕_{j+1}` is a domain: products of nonzero homogeneous
elements are nonzero. -/
theorem mul_not_mem_𝓕 {a b : ℕ} {f g : A} (hf : f ∈ S.𝓕 a) (hf1 : f ∉ S.𝓕 (a + 1))
    (hg : g ∈ S.𝓕 b) (hg1 : g ∉ S.𝓕 (b + 1)) : f * g ∉ S.𝓕 (a + b + 1) := by
  simp only [← S.fil_F] at hf hf1 hg hg1 ⊢
  exact compFil_mul_not_mem S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw hf hf1 hg hg1

/-- **Lemma 3.5(5)**: `𝓡/s𝓡` is a domain; hence `s` is a prime element of `𝓡`. -/
theorem isDomain_quotient_s : IsDomain (S.𝓡 ⧸ Ideal.span {S.s}) := by
  rw [Ideal.Quotient.isDomain_iff_prime]
  exact rees_s_prime S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw

theorem prime_s : Prime S.s := by
  have hs0 : S.s ≠ 0 := by
    intro h
    have := congrArg (fun r : S.𝓡 => (r : A[T;T⁻¹])) h
    simp only [s_coe, ZeroMemClass.coe_zero] at this
    exact (isUnit_T (-1 : ℤ)).ne_zero this
  exact (Ideal.span_singleton_prime hs0).1 (rees_s_prime S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw)

/-! ## Theorem 3.6 -/

/-- **Theorem 3.6** (`thm:drop`, strict decrease of the invariant). Let `P` be a maximal ideal of
`𝓡` that contains `I_w + s𝓡` but not `𝓡plus`. Then `inv_P(I_w) ≺ maxinv(I)`. -/
theorem drop (P : Ideal S.𝓡) [P.IsMaximal] (hIw : S.Iw ≤ P) (hs : S.s ∈ P)
    (hP : ¬ S.𝓡plus ≤ P) : inv S.Iw P ≺ maxinv S.I := by
  -- some generator `f T^j` (`j ≥ 1`) of `𝓡₊` lies outside `P`
  obtain ⟨r, ⟨j, f, hj1, hf, hr⟩, hrP⟩ : ∃ r ∈ {r : S.𝓡 | ∃ (j : ℤ) (f : A), 1 ≤ j ∧
      f ∈ S.𝓕 j ∧ (r : A[T;T⁻¹]) = C f * T j}, r ∉ P := by
    by_contra h
    push Not at h
    exact hP (Ideal.span_le.2 fun r hr => h r hr)
  have hIw0 : S.Iw ≠ ⊥ := weakT_ne_bot S.fil S.ne_bot S.d S.I_le_fil
  have hv := invAt_inv hIw0 hIw
  rw [weightLT_iff]
  have hf' : f ∈ S.fil.F j := by rw [S.fil_F]; exact hf
  have hrP' : (⟨C f * T j, C_mul_T_mem_ReesAlg hf'⟩ : S.𝓡) ∉ P := by
    have : r = ⟨C f * T j, C_mul_T_mem_ReesAlg hf'⟩ := Subtype.ext hr
    rwa [this] at hrP
  exact Principalization.drop S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw P hIw hs hj1 hf' hrP' hv

end ReesData

/-! ## Lemma 3.7 -/

/-- The extension of a derivation `δ` of `A` to `A_𝔪`. -/
abbrev derivLoc (δ : Derivation ℚ A A) (𝔪 : Ideal A) [𝔪.IsPrime] :
    Derivation ℚ (Localization.AtPrime 𝔪) (Localization.AtPrime 𝔪) :=
  extLoc (S := Localization.AtPrime 𝔪) 𝔪.primeCompl δ

/-- **Lemma 3.7(1)** (`lem:derivations`): a `ℚ`-derivation `δ` of `A` with `δ(I) ⊆ I` preserves the
maximal center: `δ(F_t(𝔪)) ⊆ F_t(𝔪)` for every `t` (with `δ` extended to `A_𝔪`). -/
theorem deriv_mem_maxCenter {I : Ideal A} (hI : I ≠ ⊥) {𝔪 : Ideal A} [𝔪.IsMaximal]
    (hI𝔪 : I ≤ 𝔪) (δ : Derivation ℚ A A) (hδ : ∀ f ∈ I, δ f ∈ I) (t : ℚ)
    {f : Localization.AtPrime 𝔪} (hf : f ∈ maxCenter I 𝔪 t) :
    derivLoc δ 𝔪 f ∈ maxCenter I 𝔪 t := by
  rw [maxCenter_eq_cRF hI hI𝔪] at hf ⊢
  obtain ⟨n, e, he, -⟩ := invAt_inv hI hI𝔪
  obtain ⟨J, -, -⟩ := he.1
  obtain ⟨k, ck, hrun, hadm, hck, hsupp⟩ :=
    he.exists_run (Iloc_ne_bot hI 𝔪) (Iloc_le hI𝔪) J.c J.centred
  have hδ𝔪 : ∀ g ∈ Iloc I 𝔪, derivLoc δ 𝔪 g ∈ Iloc I 𝔪 := fun g hg =>
    deriv_mem_map (algebraMap A _) (derivLoc δ 𝔪) δ (fun r => extLoc_algebraMap _ δ r) hδ hg
  have hx : ∀ i, e i ≠ 0 → derivLoc δ 𝔪 (ck.x i) ∈ ck.RF e (e i) := fun i hi =>
    deriv_mem_RF hrun hadm hck he.nonneg he.anti hsupp _ hδ𝔪 i ((hsupp i).1 hi)
  have hcRF : cRF I 𝔪 t = ck.RF e t :=
    cRF_eq hI hI𝔪 (J := ⟨ck, e, hck, he.nonneg, he.anti⟩) hadm he t
  rw [hcRF] at hf ⊢
  exact deriv_mem_RF_of_x ck (derivLoc δ 𝔪) hx t hf

/-- **Lemma 3.7(1)**: consequently `δ(𝓕_j) ⊆ 𝓕_j` in Notation 3.4. -/
theorem ReesData.deriv_mem_𝓕 (S : ReesData A) (δ : Derivation ℚ A A)
    (hδ : ∀ f ∈ S.I, δ f ∈ S.I) (j : ℤ) {f : A} (hf : f ∈ S.𝓕 j) : δ f ∈ S.𝓕 j := by
  rw [← S.fil_F] at hf ⊢
  exact deriv_mem_compF S.ne_bot S.hmax S.h𝔭 δ hδ _ hf

/-- **Lemma 3.7(2)** (`lem:derivations`): if `δ₁, …, δ_m` are derivations of `A` with
`δⱼ(I) ⊆ I` and `det(δⱼ(z_q)) ∉ 𝔪` for some `z₁, …, z_m ∈ A`, then `inv_𝔪(I)` has at most
`dim A - m` nonzero entries. -/
theorem numNonzero_inv_add_le {I : Ideal A} (hI : I ≠ ⊥) {𝔪 : Ideal A} [𝔪.IsMaximal]
    (hI𝔪 : I ≤ 𝔪) {m : ℕ} (δ : Fin m → Derivation ℚ A A) (hδ : ∀ j, ∀ f ∈ I, δ j f ∈ I)
    (z : Fin m → A) (hz : (Matrix.of fun j q => δ j (z q)).det ∉ 𝔪) :
    ((numNonzero (inv I 𝔪) + m : ℕ) : WithBot ℕ∞) ≤ ringKrullDim A := by
  obtain ⟨n, e, he, hext⟩ := invAt_inv hI hI𝔪
  obtain ⟨J, -, -⟩ := he.1
  obtain ⟨k, ck, hrun, hadm, hck, hsupp⟩ :=
    he.exists_run (Iloc_ne_bot hI 𝔪) (Iloc_le hI𝔪) J.c J.centred
  have hunit : IsUnit (Matrix.of fun j l => derivLoc (δ j) 𝔪
      (algebraMap A (Localization.AtPrime 𝔪) (z l))).det := by
    rw [det_extLoc]
    exact IsLocalization.map_units (Localization.AtPrime 𝔪) (⟨_, hz⟩ : 𝔪.primeCompl)
  have hkm := length_le_of_derivations hrun hadm hck he.nonneg he.anti hsupp
    (fun j => derivLoc (δ j) 𝔪)
    (fun j g hg => deriv_mem_map (algebraMap A _) (derivLoc (δ j) 𝔪) (δ j)
      (fun r => extLoc_algebraMap _ (δ j) r) (hδ j) hg) _ hunit
  have hk : numNonzero (inv I 𝔪) = k := by
    rw [← hext]
    unfold numNonzero
    have : {i | ext0 e i ≠ 0} = ↑(Finset.range k) := by
      ext i
      simp only [Set.mem_ofPred_eq, Finset.coe_range, Set.mem_Iio]
      by_cases hin : i < n
      · rw [show ext0 e i = e ⟨i, hin⟩ by simp [ext0, hin]]
        exact hsupp ⟨i, hin⟩
      · rw [show ext0 e i = 0 by simp [ext0, hin]]
        simp only [ne_eq, not_true_eq_false, false_iff, not_lt]
        omega
    rw [this, Set.ncard_coe_finset, Finset.card_range]
  rw [chart_size_eq_ringKrullDim J.c, hk]
  exact_mod_cast hkm

end BezoutCounterexample
