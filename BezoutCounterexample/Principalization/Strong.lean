import BezoutCounterexample.Principalization.RealPts

/-!
# Proposition 4.6, strengthened (Remark 4.7)

The principalization of `principalizationExtension` has more properties than Proposition 4.6
states (`principalizationExtension_strong`):

* (a) `K' → K` is injective over `K ∖ V(I)(ℝ)` (`InjAway`) and restricts to a homeomorphism there
  (`isHomeomorph_away`). The fibres of the weighted sphere bundle over points that do not kill the
  centre are single points (`torsorK_injAway`).
* (b) `A → A'` is of finite presentation and formally smooth at every prime of `A'` not containing
  `IA'` (`SmoothAway`), so `A → A'_{f(a)}` is smooth for `a ∈ I`
  (`SmoothAway.smooth_localization`). In the torsor step, away from `V(𝔭)` the Rees algebra is
  `A_a[T, T⁻¹]` (`reesAlg_loc_away_top`) and the torsor is a Jouanolou device over it
  (`torsor_formallySmooth_away`).
* (c) `IA' = tA'` where `t` is a unit times a product of primes `p` with `IA' ⊆ pA'`.

The induction is the one in `Induction.lean`; `StepPropS` and `PrincConclS` carry the extra
properties (`princ_of_stepS`, `stepPropS`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

/-- Laurent polynomials are formally smooth over the base. -/
theorem laurent_formallySmooth_base (B : Type*) [CommRing B] :
    Algebra.FormallySmooth B B[T;T⁻¹] := by
  have : Algebra.FormallySmooth (Polynomial B) B[T;T⁻¹] :=
    Algebra.FormallySmooth.of_isLocalization (Submonoid.powers (Polynomial.X : Polynomial B))
  exact Algebra.FormallySmooth.comp B (Polynomial B) B[T;T⁻¹]

lemma reesMap_algebraMap {B : Type*} [CommRing B] [Algebra ℚ B] (Φ : WFil B) (L : Type*)
    [CommRing L] [Algebra ℚ L] [Algebra B L] (b : B) :
    reesMap Φ L (algebraMap B (ReesAlg Φ) b) = algebraMap L (ReesAlg (Φ.loc L)) (algebraMap B L b) := by
  apply Subtype.ext
  show lmap (algebraMap B L) (algebraMap B B[T;T⁻¹] b) = algebraMap L L[T;T⁻¹] (algebraMap B L b)
  rw [← LaurentPolynomial.C_eq_algebraMap, ← LaurentPolynomial.C_eq_algebraMap]
  ext m
  rw [lmap_coeff, LaurentPolynomial.C_apply, LaurentPolynomial.C_apply]
  split_ifs <;> simp

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)

include hI hmax h𝔭 hd hw in
/-- Away from `V(𝔭)` the component filtration is trivial. -/
theorem compFil_loc_away_top {a : A} (ha : a ∈ 𝔭) (j : ℤ) :
    ((compFil hI hmax h𝔭 d).F j).map (algebraMap A (Localization.Away a)) = ⊤ := by
  rcases le_or_gt j 0 with hj | hj
  · rw [compFil_F_nonpos hI hmax h𝔭 d hj, Ideal.map_top]
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, j = N := ⟨j.toNat, (Int.toNat_of_nonneg hj.le).symm⟩
    have hmem : a ^ N ∈ (compFil hI hmax h𝔭 d).F N := by
      rw [compFil_F]
      have := pow_le_compF hI hmax h𝔭 hd hw N (Ideal.pow_mem_pow ha N)
      simpa using this
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hmem)
      (by rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit a).pow N)

include hI hmax h𝔭 hd hw in
theorem reesAlg_loc_away_top {a : A} (ha : a ∈ 𝔭) :
    ReesAlg ((compFil hI hmax h𝔭 d).loc (Localization.Away a)) = ⊤ := by
  rw [eq_top_iff]
  intro p _ j
  show p.coeff j ∈ ((compFil hI hmax h𝔭 d).F j).map _
  rw [compFil_loc_away_top hI hmax h𝔭 hd hw ha]; trivial

include hI hmax h𝔭 hd hw in
/-- Away from `V(𝔭)` the Rees algebra is a Laurent polynomial ring, hence formally smooth. -/
theorem reesLocAway_formallySmooth {a : A} (ha : a ∈ 𝔭) :
    Algebra.FormallySmooth (Localization.Away a)
      (ReesAlg ((compFil hI hmax h𝔭 d).loc (Localization.Away a))) := by
  have := laurent_formallySmooth_base (Localization.Away a)
  exact Algebra.FormallySmooth.of_equiv ((Subalgebra.equivOfEq _ _
    (reesAlg_loc_away_top hI hmax h𝔭 hd hw ha)).trans Subalgebra.topEquiv).symm

end BezoutCounterexample.Principalization

namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

/-- Formal smoothness at a prime from formal smoothness of a localization avoiding it. -/
theorem formallySmooth_atPrime_of_localization {A U U' : Type*} [CommRing A] [CommRing U]
    [CommRing U'] [Algebra A U] [Algebra U U'] (M' : Submonoid U) [IsLocalization M' U']
    (P : Ideal U) [P.IsPrime] (hM' : M' ≤ P.primeCompl)
    (h : ((algebraMap U U').comp (algebraMap A U)).FormallySmooth) :
    Algebra.FormallySmooth A (Localization.AtPrime P) := by
  let : Algebra U' (Localization.AtPrime P) :=
    localizationAlgebraOfSubmonoidLe U' (Localization.AtPrime P) M' P.primeCompl hM'
  have : IsScalarTower U U' (Localization.AtPrime P) :=
    localization_isScalarTower_of_submonoid_le U' (Localization.AtPrime P) M' P.primeCompl hM'
  have : IsLocalization (Algebra.algebraMapSubmonoid U' P.primeCompl) (Localization.AtPrime P) :=
    isLocalization_of_submonoid_le U' (Localization.AtPrime P) M' P.primeCompl hM'
  have h4 : (algebraMap U' (Localization.AtPrime P)).FormallySmooth :=
    RingHom.formallySmooth_algebraMap.2
      (Algebra.FormallySmooth.of_isLocalization (Algebra.algebraMapSubmonoid U' P.primeCompl))
  rw [← RingHom.formallySmooth_algebraMap]
  convert h.comp h4 using 1
  ext x
  rw [RingHom.comp_apply, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)

local notation "Φ" => compFil hI hmax h𝔭 d
local notation "U" => Torsor hI hmax h𝔭 d hπ

include hI hmax h𝔭 hd hw in
/-- **The torsor step is smooth away from `V(𝔭)`**: at a prime `P` of the torsor not containing
`a ∈ 𝔭`, the local ring `U_P` is formally smooth over `A`. -/
theorem torsor_formallySmooth_away {a : A} (ha : a ∈ 𝔭) (P : Ideal U)
    [P.IsPrime] (haP : algebraMap A U a ∉ P) :
    Algebra.FormallySmooth A (Localization.AtPrime P) := by
  classical
  have ha0 : a ≠ 0 := by rintro rfl; exact haP (by rw [map_zero]; exact P.zero_mem)
  have hM : Submonoid.powers a ≤ nonZeroDivisors A := powers_le_nonZeroDivisors_of_noZeroDivisors ha0
  let : Algebra (ReesAlg Φ) (ReesAlg (WFil.loc Φ (Localization.Away a))) :=
    (reesMap Φ (Localization.Away a)).toAlgebra
  have hloc1 : IsLocalization ((Submonoid.powers a).map (algebraMap A (ReesAlg Φ)))
      (ReesAlg (WFil.loc Φ (Localization.Away a))) :=
    reesMap_isLocalization Φ (Localization.Away a) (Submonoid.powers a) hM
  let : Algebra U (Jou.J (algebraMap (ReesAlg Φ) (ReesAlg (WFil.loc Φ (Localization.Away a))) ∘
      torsorY hI hmax h𝔭 d hπ)) :=
    (Jou.map (algebraMap (ReesAlg Φ) (ReesAlg (WFil.loc Φ (Localization.Away a))))
      (torsorY hI hmax h𝔭 d hπ)).toAlgebra
  have hloc2 : IsLocalization (((Submonoid.powers a).map (algebraMap A (ReesAlg Φ))).map
      (algebraMap (ReesAlg Φ) U))
      (Jou.J (algebraMap (ReesAlg Φ) (ReesAlg (WFil.loc Φ (Localization.Away a))) ∘
        torsorY hI hmax h𝔭 d hπ)) :=
    Jou.isLocalization_map (torsorY hI hmax h𝔭 d hπ)
      ((Submonoid.powers a).map (algebraMap A (ReesAlg Φ)))
  have hM' : ((Submonoid.powers a).map (algebraMap A (ReesAlg Φ))).map (algebraMap (ReesAlg Φ) U)
      ≤ P.primeCompl := by
    rintro _ ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩, rfl⟩
    show _ ∉ P
    rw [map_pow, map_pow, ← IsScalarTower.algebraMap_apply]
    exact fun h => haP (‹P.IsPrime›.mem_of_pow_mem n h)
  refine formallySmooth_atPrime_of_localization (U' := Jou.J (algebraMap (ReesAlg Φ)
    (ReesAlg (WFil.loc Φ (Localization.Away a))) ∘ torsorY hI hmax h𝔭 d hπ)) _ P hM' ?_
  -- the chain `A → A_a → R' → U'` of formally smooth maps
  have h1 : (algebraMap A (Localization.Away a)).FormallySmooth :=
    RingHom.formallySmooth_algebraMap.2
      (Algebra.FormallySmooth.of_isLocalization (Submonoid.powers a))
  have h2 : (algebraMap (Localization.Away a) (ReesAlg (WFil.loc Φ (Localization.Away a)))).FormallySmooth :=
    RingHom.formallySmooth_algebraMap.2 (reesLocAway_formallySmooth hI hmax h𝔭 hd hw ha)
  have h3 := RingHom.formallySmooth_algebraMap.2 (Jou.formallySmooth
    (algebraMap (ReesAlg Φ) (ReesAlg (WFil.loc Φ (Localization.Away a))) ∘ torsorY hI hmax h𝔭 d hπ))
  have hchain := (h1.comp h2).comp h3
  convert hchain using 1
  ext x
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply A (ReesAlg Φ) U]
  show Jou.map (algebraMap (ReesAlg Φ) (ReesAlg (WFil.loc Φ (Localization.Away a))))
    (torsorY hI hmax h𝔭 d hπ) (algebraMap (ReesAlg Φ) U (algebraMap A (ReesAlg Φ) x)) = _
  rw [Jou.map_algebraMap]
  congr 1
  exact reesMap_algebraMap Φ (Localization.Away a) x

end BezoutCounterexample.Principalization

namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

/-! ### Smoothness and injectivity away from the centre -/

/-- `f : A → A'` is *formally smooth away from `V(I)`*: at every prime `P` of `A'` not containing
`I A'`, the local ring `A'_P` is formally smooth over `A`. -/
def SmoothAway {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A') (I : Ideal A) : Prop :=
  ∀ (P : Ideal A') [P.IsPrime], ¬ I.map f ≤ P →
    ((algebraMap A' (Localization.AtPrime P)).comp f).FormallySmooth

lemma smoothAway_id {A : Type} [CommRing A] (I : Ideal A) : SmoothAway (RingHom.id A) I := by
  intro P _ _
  rw [RingHom.comp_id]
  exact RingHom.formallySmooth_algebraMap.2 (Algebra.FormallySmooth.of_isLocalization P.primeCompl)

lemma SmoothAway.comp {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A'']
    {f : A →+* A'} {g : A' →+* A''} {I : Ideal A} {I' : Ideal A'} (hf : SmoothAway f I)
    (hg : SmoothAway g I') (hII' : I.map f ≤ I') : SmoothAway (g.comp f) I := by
  intro P'' _ hP''
  have : (P''.comap g).IsPrime := Ideal.comap_isPrime g P''
  have h1 : ¬ I.map f ≤ P''.comap g := by
    intro h
    apply hP''
    rw [← Ideal.map_map]
    exact Ideal.map_le_iff_le_comap.2 h
  have h2 : ¬ I'.map g ≤ P'' := by
    intro h
    apply hP''
    rw [← Ideal.map_map]
    exact (Ideal.map_mono hII').trans h
  have hf' := hf (P''.comap g) h1
  have hg' := hg P'' h2
  let : Algebra A' (Localization.AtPrime P'') := ((algebraMap A'' _).comp g).toAlgebra
  let : Algebra (Localization.AtPrime (P''.comap g)) (Localization.AtPrime P'') :=
    (Localization.localRingHom (P''.comap g) P'' g rfl).toAlgebra
  have : IsScalarTower A' (Localization.AtPrime (P''.comap g)) (Localization.AtPrime P'') :=
    IsScalarTower.of_algebraMap_eq
      (fun x => (Localization.localRingHom_to_map (P''.comap g) P'' g rfl x).symm)
  have : Algebra.FormallySmooth A' (Localization.AtPrime P'') := hg'
  have h3 : Algebra.FormallySmooth (Localization.AtPrime (P''.comap g))
      (Localization.AtPrime P'') := Algebra.FormallySmooth.localization_base (P''.comap g).primeCompl
  have h4 := hf'.comp (RingHom.formallySmooth_algebraMap.2 h3)
  convert h4 using 1
  ext x
  simp only [RingHom.comp_apply]
  exact (Localization.localRingHom_to_map (P''.comap g) P'' g rfl (f x)).symm

/-- Points of `K'` over points outside `V(I)(ℝ)` are determined by their images. -/
def InjAway {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A') (I : Ideal A)
    (K' : Set (RealPt A')) : Prop :=
  ∀ w₁ ∈ K', ∀ w₂ ∈ K', RealPt.comap f w₁ = RealPt.comap f w₂ → (∃ a ∈ I, w₁ (f a) ≠ 0) →
    w₁ = w₂

lemma injAway_id {A : Type} [CommRing A] (I : Ideal A) (K : Set (RealPt A)) :
    InjAway (RingHom.id A) I K := by
  intro w₁ _ w₂ _ h _
  ext a
  exact congrArg (fun z : RealPt A => z a) h

lemma InjAway.comp {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A'']
    {f : A →+* A'} {g : A' →+* A''} {I : Ideal A} {I' : Ideal A'} {K' : Set (RealPt A')}
    {K'' : Set (RealPt A'')} (hf : InjAway f I K') (hg : InjAway g I' K'')
    (hmaps : Set.MapsTo (RealPt.comap g) K'' K') (hII' : I.map f ≤ I') :
    InjAway (g.comp f) I K'' := by
  rintro w₁ hw₁ w₂ hw₂ h ⟨a, ha, ha0⟩
  have hv : RealPt.comap g w₁ = RealPt.comap g w₂ :=
    hf _ (hmaps hw₁) _ (hmaps hw₂) h ⟨a, ha, ha0⟩
  exact hg w₁ hw₁ w₂ hw₂ hv ⟨f a, hII' (Ideal.mem_map_of_mem f ha), ha0⟩

/-- **Isomorphism away from the centre**: a monotone surjection `K' → K` of compact sets which is
injective over `K ∖ V(I)(ℝ)` restricts to a homeomorphism over `K ∖ V(I)(ℝ)`. -/
theorem isHomeomorph_away {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A')
    (I : Ideal A) {K : Set (RealPt A)} {K' : Set (RealPt A')} (hK' : IsCompact K')
    (hmono : IsMonotoneSurjOn (RealPt.comap f) K' K) (hinj : InjAway f I K') :
    IsHomeomorph (({z : K | ∃ a ∈ I, z.1 a ≠ 0}).restrictPreimage
      (hmono.1.restrict (RealPt.comap f) K' K)) := by
  obtain ⟨hmaps, hq⟩ := hmono
  have : CompactSpace K' := isCompact_iff_compactSpace.1 hK'
  rw [isHomeomorph_iff_continuous_isClosedMap_bijective]
  refine ⟨hq.continuous.restrictPreimage, (hq.continuous.isClosedMap).restrictPreimage _,
    ⟨fun w₁ w₂ h => ?_, fun z => ?_⟩⟩
  · obtain ⟨a, ha, ha0⟩ := w₁.2
    have h' : RealPt.comap f w₁.1.1 = RealPt.comap f w₂.1.1 :=
      congrArg (fun z : K => z.1) (congrArg Subtype.val h)
    exact Subtype.ext (Subtype.ext (hinj _ w₁.1.2 _ w₂.1.2 h' ⟨a, ha, ha0⟩))
  · obtain ⟨w, hw⟩ := hq.surjective z.1
    refine ⟨⟨w, ?_⟩, Subtype.ext hw⟩
    show hmaps.restrict (RealPt.comap f) K' K w ∈ {z : K | ∃ a ∈ I, z.1 a ≠ 0}
    rw [hw]
    exact z.2

end BezoutCounterexample.Principalization

namespace BezoutCounterexample.Principalization

open LaurentPolynomial Jou IsLocalRing Topology

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)

include hd hw in
/-- The weighted sphere bundle maps monotonically onto `K` (the content of `torsorRealPts`). -/
theorem torsorK_monotone (hk2 : v₀ 1 ≠ 0) (K : Set (RealPt A)) :
    IsMonotoneSurjOn (RealPt.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)))
      (torsorK hI hmax h𝔭 hπ K) K := by
  have hmaps : Set.MapsTo (RealPt.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)))
      (torsorK hI hmax h𝔭 hπ K) K := fun w hw => hw.1
  refine ⟨hmaps, ⟨?_, ?_, ?_⟩⟩
  · exact ((RealPt.continuous_comap _).comp continuous_subtype_val).subtype_mk _
  · rintro ⟨z, hzK⟩
    rcases (gNorm_nonneg hI hmax h𝔭 (d := d) (π := π) z).lt_or_eq with hpos | h0
    · exact ⟨⟨ptA hI hmax h𝔭 hd hπ z hpos, ptA_mem hI hmax h𝔭 hd hπ K hzK hpos⟩,
        Subtype.ext (ptA_comap hI hmax h𝔭 hd hπ z hpos)⟩
    · have hz := kills_of_gNorm_zero hI hmax h𝔭 hd hw hπ h0.symm
      obtain ⟨P⟩ := LocPres.nonempty hI hmax h𝔭 hw z hz
      have hk : 0 < P.k := by have := P.hk2 hk2; omega
      set u : ({0}ᶜ : Set (Fin P.k → ℝ)) := ⟨fun _ => 1, fun h => by
        have := congrFun h ⟨0, hk⟩; simp at this⟩
      exact ⟨⟨P.Gamma hI hmax h𝔭 hd hz hπ u, P.Gamma_mem hI hmax h𝔭 hd hz hπ hzK u⟩,
        Subtype.ext (P.Gamma_comap hI hmax h𝔭 hd hz hπ u)⟩
  · rintro ⟨z, hzK⟩
    apply isConnected_restrict_fiber
    show IsConnected (torsorFib hI hmax h𝔭 hπ K z)
    rcases (gNorm_nonneg hI hmax h𝔭 (d := d) (π := π) z).lt_or_eq with hpos | h0
    · have : torsorFib hI hmax h𝔭 hπ K z = {ptA hI hmax h𝔭 hd hπ z hpos} := by
        ext w
        constructor
        · rintro ⟨hwK, hwz⟩
          exact eq_ptA hI hmax h𝔭 hd hπ K hwK hwz hpos
        · rintro rfl
          exact ⟨ptA_mem hI hmax h𝔭 hd hπ K hzK hpos, ptA_comap hI hmax h𝔭 hd hπ z hpos⟩
      rw [this]
      exact isConnected_singleton
    · exact fib_connected hI hmax h𝔭 hd hw hπ (kills_of_gNorm_zero hI hmax h𝔭 hd hw hπ h0.symm)
        hk2 hzK

include hd hw in
/-- **The torsor step is injective over `K ∖ V(𝔭)(ℝ)`**: the fibre of the weighted sphere bundle
over a real point not killing `𝔭` is a single point. -/
theorem torsorK_injAway (hI𝔭 : I ≤ 𝔭) (K : Set (RealPt A)) :
    InjAway (algebraMap A (Torsor hI hmax h𝔭 d hπ)) I (torsorK hI hmax h𝔭 hπ K) := by
  rintro w₁ hw₁ w₂ hw₂ h ⟨a, ha, ha0⟩
  have hz : 0 < gNorm hI hmax h𝔭 d π (RealPt.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) w₁) := by
    rcases (gNorm_nonneg hI hmax h𝔭 (d := d) (π := π)
      (RealPt.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) w₁)).lt_or_eq with hpos | h0
    · exact hpos
    · exact absurd (kills_of_gNorm_zero hI hmax h𝔭 hd hw hπ h0.symm a (hI𝔭 ha)) ha0
  rw [eq_ptA hI hmax h𝔭 hd hπ K hw₁ rfl hz, eq_ptA hI hmax h𝔭 hd hπ K hw₂ h.symm hz]

include hd hw in
/-- **The torsor step is smooth away from `V(I)`.** -/
theorem torsor_smoothAway (hI𝔭 : I ≤ 𝔭) :
    SmoothAway (algebraMap A (Torsor hI hmax h𝔭 d hπ)) I := by
  intro P _ hP
  obtain ⟨a, ha, haP⟩ : ∃ a ∈ I, algebraMap A (Torsor hI hmax h𝔭 d hπ) a ∉ P := by
    by_contra hcon
    push Not at hcon
    exact hP (Ideal.map_le_iff_le_comap.2 fun a ha => hcon a ha)
  have := torsor_formallySmooth_away hI hmax h𝔭 hd hw hπ (hI𝔭 ha) P haP
  rw [← IsScalarTower.algebraMap_eq]
  exact RingHom.formallySmooth_algebraMap.2 this

end BezoutCounterexample.Principalization

namespace BezoutCounterexample.Principalization

open IsLocalRing

/-- The step of the principalization algorithm, with the extra properties away from `V(I)`. -/
def StepPropS (N : ℕ) : Prop :=
  ∀ (A : SmoothFactorialDomain) (I : Ideal A) (K : Set (RealPt A)) (m : ℕ) (v₀ : ℕ → ℚ),
    I ≠ ⊥ → IsCompact K → VertOK I m → DimOK I m N → MaxInv I v₀ →
    ∃ (A' : SmoothFactorialDomain) (f : A →ₐ[ℚ] A') (K' : Set (RealPt A')) (I' : Ideal A')
      (t : A') (m' : ℕ),
      Function.Injective f ∧ I.map f = Ideal.span {t} * I' ∧ I' ≠ ⊥ ∧ IsCompact K' ∧
      IsMonotoneSurjOn (RealPt.comap (f : A →+* A')) K' K ∧ VertOK I' m' ∧ DimOK I' m' N ∧
      (∀ v₀', MaxInv I' v₀' → measureW N I' v₀' < measureW N I v₀) ∧
      InjAway (f : A →+* A') I K' ∧ SmoothAway (f : A →+* A') I

/-- The strengthened conclusion of the principalization theorem. -/
def PrincConclS (A : SmoothFactorialDomain) (I : Ideal A) (K : Set (RealPt A)) : Prop :=
  ∃ (A' : SmoothFactorialDomain) (f : A →ₐ[ℚ] A') (K' : Set (RealPt A')) (t : A'),
    Function.Injective f ∧ I.map f = Ideal.span {t} ∧ IsCompact K' ∧
      IsMonotoneSurjOn (RealPt.comap (f : A →+* A')) K' K ∧
      InjAway (f : A →+* A') I K' ∧ SmoothAway (f : A →+* A') I

lemma princConclS_top (A : SmoothFactorialDomain) (K : Set (RealPt A)) (hK : IsCompact K) :
    PrincConclS A ⊤ K :=
  ⟨A, AlgHom.id ℚ A, K, 1, Function.injective_id, by simp, hK, IsMonotoneSurjOn.id' K,
    injAway_id ⊤ K, smoothAway_id ⊤⟩

/-- Composition: principalizing `I'` after a step principalizes `I`. -/
lemma princConclS_of_step {A A' : SmoothFactorialDomain} {I : Ideal A} {K : Set (RealPt A)}
    (f : A →ₐ[ℚ] A') (K' : Set (RealPt A')) (I' : Ideal A') (t : A')
    (hinj : Function.Injective f) (hmap : I.map f = Ideal.span {t} * I')
    (hmono : IsMonotoneSurjOn (RealPt.comap (f : A →+* A')) K' K)
    (hia : InjAway (f : A →+* A') I K') (hsa : SmoothAway (f : A →+* A') I)
    (h : PrincConclS A' I' K') : PrincConclS A I K := by
  obtain ⟨A'', g, K'', u, hginj, hu, hK'', hgmono, hgia, hgsa⟩ := h
  have hII' : I.map (f : A →+* A') ≤ I' := hmap ▸ Ideal.mul_le_right
  refine ⟨A'', g.comp f, K'', g t * u, hginj.comp hinj, ?_, hK'', ?_, ?_, ?_⟩
  · have : (I.map (g.comp f) : Ideal A'') = (I.map f).map g :=
      (Ideal.map_map (f : A →+* A') (g : A' →+* A'')).symm
    rw [this, hmap, Ideal.map_mul, hu, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_mul_span_singleton]
  · exact IsMonotoneSurjOn.comap_comp (f : A →+* A') (g : A' →+* A'') hK'' hmono hgmono
  · exact hia.comp hgia hgmono.1 hII'
  · exact hsa.comp hgsa hII'

/-- **Well-founded induction** on the measure, for the strengthened conclusion. -/
theorem princ_of_stepS (N : ℕ) (step : StepPropS N) :
    ∀ (A : SmoothFactorialDomain) (I : Ideal A) (K : Set (RealPt A)) (m : ℕ),
      I ≠ ⊥ → IsCompact K → VertOK I m → DimOK I m N → PrincConclS A I K := by
  suffices H : ∀ μ : Lex (Fin N → WithTop ℕ) ×ₗ ℕ, ∀ (A : SmoothFactorialDomain) (I : Ideal A)
      (K : Set (RealPt A)) (m : ℕ) (v₀ : ℕ → ℚ), I ≠ ⊥ → IsCompact K → VertOK I m →
      DimOK I m N → MaxInv I v₀ → measureW N I v₀ = μ → PrincConclS A I K by
    intro A I K m hI hK hV hD
    by_cases htop : I = ⊤
    · subst htop; exact princConclS_top A K hK
    obtain ⟨v₀, hv₀⟩ := exists_maxInv hI htop
    exact H _ A I K m v₀ hI hK hV hD hv₀ rfl
  intro μ
  induction μ using WellFoundedLT.induction with
  | _ μ ih =>
    intro A I K m v₀ hI hK hV hD hv₀ hμ
    obtain ⟨A', f, K', I', t, m', hinj, hmap, hI', hK', hmono, hV', hD', hlt, hia, hsa⟩ :=
      step A I K m v₀ hI hK hV hD hv₀
    refine princConclS_of_step f K' I' t hinj hmap hmono hia hsa ?_
    by_cases htop : I' = ⊤
    · subst htop; exact princConclS_top A' K' hK'
    obtain ⟨v₀', hv₀'⟩ := exists_maxInv hI' htop
    exact ih _ (hμ ▸ hlt v₀' hv₀') A' I' K' m' v₀' hI' hK' hV' hD' hv₀' rfl

set_option maxHeartbeats 1000000 in
/-- **The step of the algorithm**, with the extra properties away from `V(I)`. -/
theorem stepPropS (N : ℕ) : StepPropS N := by
  intro A I K m v₀ hI hK hV hD hv₀
  obtain ⟨⟨𝔪₀, h𝔪₀, hI𝔪₀, hv𝔪₀⟩, hmax⟩ := hv₀
  have hgood : GoodV v₀ := hv𝔪₀.goodV hI hI𝔪₀
  have hz : ∀ i, N ≤ i → v₀ i = 0 := invAt_eq_zero_of_ok hI hV hD 𝔪₀ hI𝔪₀ hv𝔪₀
  have h0 : v₀ 0 ≠ 0 := hv𝔪₀.zero_ne hI
  obtain ⟨d, hd, hw⟩ := exists_weights hgood.nonneg hz
  have hL : locusIdeal I v₀ ≤ 𝔪₀ := sInf_le ⟨h𝔪₀, hI𝔪₀, hv𝔪₀⟩
  obtain ⟨𝔭, h𝔭, -⟩ := Ideal.exists_minimalPrimes_le hL
  have hI𝔭 : I ≤ 𝔭 := (le_sInf fun 𝔪 h𝔪 => h𝔪.2.1).trans h𝔭.1.2
  have h𝔭bot : 𝔭 ≠ ⊥ := fun h => hI (eq_bot_iff.2 (h ▸ hI𝔭))
  obtain ⟨π, hπ𝔭, hπp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot h𝔭.1.1 h𝔭bot
  have hmeas : ∀ {A' : SmoothFactorialDomain} {I' : Ideal A'} {m' : ℕ}, I' ≠ ⊥ →
      VertOK I' m' → DimOK I' m' N →
      (∀ (Q : Ideal A') [Q.IsMaximal], I' ≤ Q → ∀ v, InvAt I' Q v → toLex v₀ ≤ toLex v) →
      (MaxInv I' v₀ → (locusIdeal I' v₀).minimalPrimes.ncard <
        (locusIdeal I v₀).minimalPrimes.ncard) →
      ∀ v₀', MaxInv I' v₀' → measureW N I' v₀' < measureW N I v₀ := by
    intro A' I' m' hI' hV' hD' hge hc v₀' hv₀'
    obtain ⟨⟨Q, hQ, hIQ, hvQ⟩, hmax'⟩ := hv₀'
    refine measure_lt_of hgood (hvQ.goodV hI' hIQ) hz
      (invAt_eq_zero_of_ok hI' hV' hD' Q hIQ hvQ) (hge Q hIQ v₀' hvQ) ?_
    rintro rfl
    exact hc ⟨⟨Q, hQ, hIQ, hvQ⟩, hmax'⟩
  by_cases hk2 : v₀ 1 = 0
  · -- the divisorial case
    obtain ⟨a, ha0, ha⟩ := hgood.zero_eq h0
    have h𝔭π := div_eq_span hI hmax h𝔭 h0 hk2 hπp hπ𝔭
    have hle := div_le_span_pow hI hmax h𝔭 hd hw h0 hk2 hπp hπ𝔭 ha
    refine ⟨A, AlgHom.id ℚ A, K, divI I π a, π ^ a, m, Function.injective_id, ?_,
      divI_ne_bot hI, hK, IsMonotoneSurjOn.id' K, div_vertOK hI hmax h𝔭 hd hw h𝔭π ha0 hV,
      div_dimOK hD, ?_, injAway_id I K, smoothAway_id I⟩
    · show I.map (RingHom.id A) = _
      rw [Ideal.map_id]; exact div_eq_mul hle
    · exact hmeas (divI_ne_bot hI) (div_vertOK hI hmax h𝔭 hd hw h𝔭π ha0 hV) (div_dimOK hD)
        (by intro Q _ hQ v hv; exact div_inv_ge hI hmax ha0 ha hle Q hQ hv)
        (fun _ => div_count hI hmax h𝔭 h𝔭π ha0 ha hle)
  · -- the torsor case
    have hπ : π ∈ (compFil hI hmax h𝔭 d).F 1 := by
      rw [compFil_F, show ((1 : ℤ) : ℚ) / d = 1 / d by push_cast; ring,
        compF_one_div hI hmax h𝔭 hd hw]
      exact hπ𝔭
    set U := torsorSFD hI hmax h𝔭 hd hw hπ hk2 hπp hπ𝔭
    refine ⟨U, IsScalarTower.toAlgHom ℚ A (Torsor hI hmax h𝔭 d hπ), torsorK hI hmax h𝔭 hπ K,
      torsorI hI hmax h𝔭 hd hπ, torsorS hI hmax h𝔭 hπ ^ d, m + (nGen hI hmax h𝔭 d + 1),
      torsor_injective hI hmax h𝔭 hπ hπp.ne_zero, ?_, torsorI_ne_bot hI hmax h𝔭 hd hπ hπp.ne_zero,
      torsorK_isCompact hI hmax h𝔭 hd hw hπ hK, torsorK_monotone hI hmax h𝔭 hd hw hπ hk2 K,
      torsor_vertOK hI hmax h𝔭 hd hw hπ hπp.ne_zero hV,
      torsor_dimOK hI hmax h𝔭 hd hw hπ hπp.ne_zero hD, ?_,
      torsorK_injAway hI hmax h𝔭 hd hw hπ hI𝔭 K, torsor_smoothAway hI hmax h𝔭 hd hw hπ hI𝔭⟩
    · exact torsor_map_eq hI hmax h𝔭 hd hπ
    · exact hmeas (torsorI_ne_bot hI hmax h𝔭 hd hπ hπp.ne_zero)
        (torsor_vertOK hI hmax h𝔭 hd hw hπ hπp.ne_zero hV)
        (torsor_dimOK hI hmax h𝔭 hd hw hπ hπp.ne_zero hD)
        (by intro Q _ hQ v hv; exact torsor_inv_ge hI hmax h𝔭 hd hw hπ hπp.ne_zero Q hQ hv)
        (fun _ => torsor_count hI hmax h𝔭 hd hw hπ hπp.ne_zero)

end BezoutCounterexample.Principalization

namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

/-- From formal smoothness at the primes outside `V(IA')` and finite presentation: for `a ∈ I`,
`A → A'_{f(a)}` is smooth. -/
theorem SmoothAway.smooth_localization {A A' : Type} [CommRing A] [CommRing A'] {f : A →+* A'}
    {I : Ideal A} (h : SmoothAway f I) (hfp : f.FinitePresentation) {a : A} (ha : a ∈ I) :
    ((algebraMap A' (Localization.Away (f a))).comp f).Smooth := by
  let : Algebra A A' := f.toAlgebra
  have hX : (algebraMap A' (Localization.Away (f a))).comp f =
      algebraMap A (Localization.Away (f a)) :=
    (IsScalarTower.algebraMap_eq A A' (Localization.Away (f a))).symm
  rw [hX, RingHom.smooth_algebraMap]
  have : Algebra.FinitePresentation A A' := RingHom.finitePresentation_algebraMap.1 hfp
  have : Algebra.FinitePresentation A' (Localization.Away (f a)) :=
    IsLocalization.Away.finitePresentation (f a)
  have : Algebra.FinitePresentation A (Localization.Away (f a)) :=
    Algebra.FinitePresentation.trans A A' (Localization.Away (f a))
  refine ⟨?_, inferInstance⟩
  rw [← Algebra.smoothLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  intro Q
  show Algebra.FormallySmooth A (Localization.AtPrime Q.asIdeal)
  set P := Q.asIdeal.comap (algebraMap A' (Localization.Away (f a)))
  have : P.IsPrime := Ideal.comap_isPrime _ _
  have hfaP : f a ∉ P := by
    intro hmem
    have : algebraMap A' (Localization.Away (f a)) (f a) ∈ Q.asIdeal := hmem
    exact Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ this
      (IsLocalization.Away.algebraMap_isUnit (f a)))
  have hIP : ¬ I.map f ≤ P := fun hle => hfaP (hle (Ideal.mem_map_of_mem f ha))
  have hP := h P hIP
  have : Algebra.FormallySmooth A (Localization.AtPrime P) := by
    rw [← RingHom.formallySmooth_algebraMap, IsScalarTower.algebraMap_eq A A']
    exact hP
  have : IsLocalization.AtPrime (Localization.AtPrime Q.asIdeal) P :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers (f a)) (Localization.AtPrime Q.asIdeal) Q.asIdeal
  let e : Localization.AtPrime Q.asIdeal ≃ₐ[A'] Localization.AtPrime P :=
    IsLocalization.algEquiv P.primeCompl _ _
  exact Algebra.FormallySmooth.of_equiv (e.restrictScalars A).symm

/-- A map between smooth `ℚ`-algebras of finite type with Noetherian source is of finite
presentation. -/
theorem SmoothFactorialDomain.finitePresentation {A A' : SmoothFactorialDomain}
    (f : A →ₐ[ℚ] A') : (f : A →+* A').FinitePresentation := by
  rw [← RingHom.FinitePresentation.of_finiteType]
  apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℚ A)
  rw [AlgHom.comp_algebraMap, RingHom.finiteType_algebraMap]
  infer_instance

end BezoutCounterexample.Principalization

namespace BezoutCounterexample.Principalization

open IsLocalRing

/-- The principalization theorem with the extra properties away from `V(I)`. -/
theorem princConclS_holds (A : SmoothFactorialDomain) (I : Ideal A) (K : Set (RealPt A))
    (hI : I ≠ ⊥) (hK : IsCompact K) : PrincConclS A I K := by
  obtain ⟨𝔪₀, h𝔪₀⟩ := Ideal.exists_maximal A
  obtain ⟨N, ⟨c₀⟩⟩ := exists_chart_atPrime 𝔪₀
  have hV : VertOK I 0 := fun 𝔪 h𝔪 _ =>
    ⟨Fin.elim0, Fin.elim0, fun j => Fin.elim0 j, by
      rw [Matrix.det_isEmpty]; exact (Ideal.ne_top_iff_one _).1 h𝔪.ne_top⟩
  have hD : DimOK I 0 N := fun 𝔪 _ _ n ⟨c⟩ => by
    have := chart_card_eq_of_domain 𝔪 𝔪₀ c c₀
    omega
  exact princ_of_stepS N (stepPropS N) A I K 0 hI hK hV hD

/-- **Proposition 4.6, strengthened** (Remark 4.7). Let `A` be a smooth finitely generated factorial
`ℚ`-domain, `I ⊂ A` a nonzero ideal and `K ⊂ Spec(A)(ℝ)` compact. There are a smooth finitely
generated factorial `ℚ`-domain `A'`, an injection `f : A ↪ A'`, a compact `K' ⊂ Spec(A')(ℝ)` and
`t ∈ A'` such that `IA' = tA'` and `K' → K` is a monotone surjection, and moreover:

* (a) *`K' → K` is an isomorphism over `K ∖ V(I)(ℝ)`*: points of `K'` over points of `K` at which
  some element of `I` does not vanish are unique, and `K' → K` restricts to a homeomorphism over
  `K ∖ V(I)(ℝ)`;
* (b) *`A → A'` is smooth away from `V(I)`*: `A'` is of finite presentation over `A`, `A'_P` is
  formally smooth over `A` for every prime `P ⊉ IA'`, and `A → A'_{f(a)}` is smooth for `a ∈ I`;
* (c) *`t` is a product of exceptional primes*: `t ≠ 0` and `t` is a unit times a product of
  primes `p` with `IA' ⊆ pA'`. -/
theorem principalizationExtension_strong (A : SmoothFactorialDomain) (I : Ideal A)
    (K : Set (RealPt A)) (hI : I ≠ ⊥) (hK : IsCompact K) :
    ∃ (A' : SmoothFactorialDomain) (f : A →ₐ[ℚ] A') (K' : Set (RealPt A')) (t : A'),
      Function.Injective f ∧ I.map f = Ideal.span {t} ∧ IsCompact K' ∧
      IsMonotoneSurjOn (RealPt.comap (f : A →+* A')) K' K ∧
      -- (a)
      (∀ w₁ ∈ K', ∀ w₂ ∈ K', RealPt.comap (f : A →+* A') w₁ = RealPt.comap (f : A →+* A') w₂ →
        (∃ a ∈ I, w₁ (f a) ≠ 0) → w₁ = w₂) ∧
      (∀ hmaps : Set.MapsTo (RealPt.comap (f : A →+* A')) K' K,
        IsHomeomorph (({z : K | ∃ a ∈ I, z.1 a ≠ 0}).restrictPreimage
          (hmaps.restrict (RealPt.comap (f : A →+* A')) K' K))) ∧
      -- (b)
      (f : A →+* A').FinitePresentation ∧
      (∀ (P : Ideal A') [P.IsPrime], ¬ I.map f ≤ P →
        ((algebraMap A' (Localization.AtPrime P)).comp (f : A →+* A')).FormallySmooth) ∧
      (∀ a ∈ I, ((algebraMap A' (Localization.Away (f a))).comp (f : A →+* A')).Smooth) ∧
      -- (c)
      t ≠ 0 ∧ ∃ (u : A'ˣ) (s : Multiset A'), (∀ p ∈ s, Prime p ∧ I.map f ≤ Ideal.span {p}) ∧
        t = s.prod * u := by
  obtain ⟨A', f, K', t, hinj, ht, hK', hmono, hia, hsa⟩ := princConclS_holds A I K hI hK
  have hfp := SmoothFactorialDomain.finitePresentation f
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.2 rfl, Ideal.map_eq_bot_iff_of_injective hinj] at ht
    exact hI ht
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod ht0
  refine ⟨A', f, K', t, hinj, ht, hK', hmono, hia, fun _ => isHomeomorph_away _ I hK' hmono hia,
    hfp, hsa, fun a ha => hsa.smooth_localization hfp ha, ht0, u,
    UniqueFactorizationMonoid.factors t, fun p hp => ⟨UniqueFactorizationMonoid.prime_of_factor p hp,
      ?_⟩, hu.symm⟩
  rw [ht, Ideal.span_singleton_le_span_singleton]
  exact UniqueFactorizationMonoid.dvd_of_mem_factors hp

end BezoutCounterexample.Principalization
