import BezoutCounterexample.Principalization.Divisorial
import BezoutCounterexample.Topology

/-!
# The principalization algorithm: step and termination

The induction in the proof of Proposition 4.6 (`prop:principalization-extension`) of the paper.

* `MaxInv`, `measureW`: the maximal invariant and the termination measure
  `(encW N v₀, #components)` in a well-founded lexicographic order.
* `stepProp`: one step (divisorial colon or weighted-blowup torsor) strictly decreases the measure,
  keeps the length-bound data, and gives a monotone surjection on compact sets of real points
  (the latter via `TorsorRealPts`).
* `princ_of_step`: well-founded induction; `principalizationExtension_of`.
-/

noncomputable section


namespace BezoutCounterexample.Principalization

open IsLocalRing

instance SmoothFactorialDomain.isNoetherianRing' (A : SmoothFactorialDomain) :
    IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℚ A

section Measure

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

/-- `v₀` is the maximal (lexicographically smallest) invariant of `I`. -/
def MaxInv (I : Ideal A) (v₀ : ℕ → ℚ) : Prop :=
  (∃ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal), I ≤ 𝔪 ∧ InvAt I 𝔪 v₀) ∧
    ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v

/-- The termination measure. -/
def measureW (N : ℕ) (I : Ideal A) (v₀ : ℕ → ℚ) : Lex (Fin N → WithTop ℕ) ×ₗ ℕ :=
  toLex (encW N v₀, (locusIdeal I v₀).minimalPrimes.ncard)

end Measure

lemma measure_lt_of {N : ℕ} {v₀ v₀' : ℕ → ℚ} {c c' : ℕ} (hg : GoodV v₀) (hg' : GoodV v₀')
    (hz : ∀ i, N ≤ i → v₀ i = 0) (hz' : ∀ i, N ≤ i → v₀' i = 0) (hle : toLex v₀ ≤ toLex v₀')
    (hc : v₀' = v₀ → c' < c) :
    (toLex (encW N v₀', c') : Lex (Fin N → WithTop ℕ) ×ₗ ℕ) < toLex (encW N v₀, c) := by
  rcases hle.lt_or_eq with hlt | heq
  · exact Prod.Lex.toLex_lt_toLex.2 (Or.inl (encW_lt hg hg' hz hz' hlt))
  · have h := toLex.injective heq
    subst h
    exact Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, hc rfl⟩)

lemma IsMonotoneSurjOn.comap_comp {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) {K : Set (RealPt A)} {K' : Set (RealPt B)}
    {K'' : Set (RealPt C)} (hK'' : IsCompact K'') (h1 : IsMonotoneSurjOn (RealPt.comap f) K' K)
    (h2 : IsMonotoneSurjOn (RealPt.comap g) K'' K') :
    IsMonotoneSurjOn (RealPt.comap (g.comp f)) K'' K := by
  obtain ⟨m1, s1⟩ := h1
  obtain ⟨m2, s2⟩ := h2
  have m : Set.MapsTo (RealPt.comap (g.comp f)) K'' K := fun z hz => m1 (m2 hz)
  refine ⟨m, ?_⟩
  haveI : CompactSpace K'' := isCompact_iff_compactSpace.1 hK''
  have heq : m.restrict (RealPt.comap (g.comp f)) K'' K =
      (m1.restrict (RealPt.comap f) K' K) ∘ (m2.restrict (RealPt.comap g) K'' K') := by
    funext z; rfl
  rw [heq]
  exact s1.comp s2

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing

/-- The step of the principalization algorithm, abstractly. -/
def StepProp (N : ℕ) : Prop :=
  ∀ (A : SmoothFactorialDomain) (I : Ideal A) (K : Set (RealPt A)) (m : ℕ) (v₀ : ℕ → ℚ),
    I ≠ ⊥ → IsCompact K → VertOK I m → DimOK I m N → MaxInv I v₀ →
    ∃ (A' : SmoothFactorialDomain) (f : A →ₐ[ℚ] A') (K' : Set (RealPt A')) (I' : Ideal A')
      (t : A') (m' : ℕ),
      Function.Injective f ∧ I.map f = Ideal.span {t} * I' ∧ I' ≠ ⊥ ∧ IsCompact K' ∧
      IsMonotoneSurjOn (RealPt.comap (f : A →+* A')) K' K ∧ VertOK I' m' ∧ DimOK I' m' N ∧
      ∀ v₀', MaxInv I' v₀' → measureW N I' v₀' < measureW N I v₀

/-- The conclusion of the principalization theorem. -/
def PrincConcl (A : SmoothFactorialDomain) (I : Ideal A) (K : Set (RealPt A)) : Prop :=
  ∃ (A' : SmoothFactorialDomain) (f : A →ₐ[ℚ] A') (K' : Set (RealPt A')),
    Function.Injective f ∧ (I.map f).IsPrincipal ∧ IsCompact K' ∧
      IsMonotoneSurjOn (RealPt.comap (f : A →+* A')) K' K

lemma IsMonotoneSurjOn.id' {X : Type*} [TopologicalSpace X] (K : Set X) :
    IsMonotoneSurjOn (fun z : X => z) K K := by
  refine ⟨Set.mapsTo_id K, ⟨continuous_id.subtype_map _, fun w => ⟨w, rfl⟩, fun z => ?_⟩⟩
  have : (Set.MapsTo.restrict (fun z : X => z) K K (Set.mapsTo_id K)) ⁻¹' {z} = {z} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h; exact Subtype.ext (congrArg Subtype.val h)
    · intro h; subst h; rfl
  rw [this]
  exact isConnected_singleton

lemma princConcl_top (A : SmoothFactorialDomain) (K : Set (RealPt A)) (hK : IsCompact K) :
    PrincConcl A ⊤ K :=
  ⟨A, AlgHom.id ℚ A, K, Function.injective_id, ⟨⟨1, by simp⟩⟩, hK, IsMonotoneSurjOn.id' K⟩

/-- Composition: principalizing `I'` after a step principalizes `I`. -/
lemma princConcl_of_step {A A' : SmoothFactorialDomain} {I : Ideal A} {K : Set (RealPt A)}
    (f : A →ₐ[ℚ] A') (K' : Set (RealPt A')) (I' : Ideal A') (t : A')
    (hinj : Function.Injective f) (hmap : I.map f = Ideal.span {t} * I')
    (hmono : IsMonotoneSurjOn (RealPt.comap (f : A →+* A')) K' K) (h : PrincConcl A' I' K') :
    PrincConcl A I K := by
  obtain ⟨A'', g, K'', hginj, ⟨⟨u, hu⟩⟩, hK'', hgmono⟩ := h
  refine ⟨A'', g.comp f, K'', hginj.comp hinj, ⟨⟨g t * u, ?_⟩⟩, hK'', ?_⟩
  · have : (I.map (g.comp f) : Ideal A'') = (I.map f).map g :=
      (Ideal.map_map (f : A →+* A') (g : A' →+* A'')).symm
    rw [this, hmap, Ideal.map_mul, hu, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_mul_span_singleton]
  · exact IsMonotoneSurjOn.comap_comp (f : A →+* A') (g : A' →+* A'') hK'' hmono hgmono

/-- **Well-founded induction** on the measure. -/
theorem princ_of_step (N : ℕ) (step : StepProp N) :
    ∀ (A : SmoothFactorialDomain) (I : Ideal A) (K : Set (RealPt A)) (m : ℕ),
      I ≠ ⊥ → IsCompact K → VertOK I m → DimOK I m N → PrincConcl A I K := by
  suffices H : ∀ μ : Lex (Fin N → WithTop ℕ) ×ₗ ℕ, ∀ (A : SmoothFactorialDomain) (I : Ideal A)
      (K : Set (RealPt A)) (m : ℕ) (v₀ : ℕ → ℚ), I ≠ ⊥ → IsCompact K → VertOK I m →
      DimOK I m N → MaxInv I v₀ → measureW N I v₀ = μ → PrincConcl A I K by
    intro A I K m hI hK hV hD
    by_cases htop : I = ⊤
    · subst htop; exact princConcl_top A K hK
    obtain ⟨v₀, hv₀⟩ := exists_maxInv hI htop
    exact H _ A I K m v₀ hI hK hV hD hv₀ rfl
  intro μ
  induction μ using WellFoundedLT.induction with
  | _ μ ih =>
    intro A I K m v₀ hI hK hV hD hv₀ hμ
    obtain ⟨A', f, K', I', t, m', hinj, hmap, hI', hK', hmono, hV', hD', hlt⟩ :=
      step A I K m v₀ hI hK hV hD hv₀
    refine princConcl_of_step f K' I' t hinj hmap hmono ?_
    by_cases htop : I' = ⊤
    · subst htop; exact princConcl_top A' K' hK'
    obtain ⟨v₀', hv₀'⟩ := exists_maxInv hI' htop
    exact ih _ (hμ ▸ hlt v₀' hv₀') A' I' K' m' v₀' hI' hK' hV' hD' hv₀' rfl

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing

section Facts

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

lemma InvAt.goodV {I : Ideal A} (hI : I ≠ ⊥) {𝔪 : Ideal A} [𝔪.IsMaximal] (hI𝔪 : I ≤ 𝔪)
    {v : ℕ → ℚ} (hv : InvAt I 𝔪 v) : GoodV v := by
  obtain ⟨n, e, he, rfl⟩ := hv
  haveI : IsNoetherianRing (Localization.AtPrime 𝔪) :=
    IsLocalization.isNoetherianRing 𝔪.primeCompl _ inferInstance
  obtain ⟨J, -, -⟩ := he.1
  exact he.goodV (Iloc_ne_bot hI 𝔪) (Iloc_le hI𝔪) J.c J.centred

lemma InvAt.zero_ne {I : Ideal A} (hI : I ≠ ⊥) {𝔪 : Ideal A} [𝔪.IsMaximal]
    {v : ℕ → ℚ} (hv : InvAt I 𝔪 v) : v 0 ≠ 0 := by
  obtain ⟨n, e, he, rfl⟩ := hv
  intro h0
  have he0 : ∀ i, e i = 0 := by
    intro i
    have hi0 : (0 : ℕ) < n := by have := i.2; omega
    have h1 : e ⟨0, hi0⟩ = 0 := by simpa [ext0, dif_pos hi0] using h0
    exact le_antisymm (h1 ▸ he.anti (Fin.le_def.2 (Nat.zero_le _))) (he.nonneg i)
  obtain ⟨⟨J, hJ, hJe⟩, -⟩ := he
  apply Iloc_ne_bot hI 𝔪
  rw [eq_bot_iff]
  refine hJ.trans ?_
  show J.c.RF J.e 1 ≤ ⊥
  rw [Chart.RF, Ideal.span_le]
  rintro _ ⟨α, hα0, hα1, rfl⟩
  exfalso
  have : lam J.e α = 0 := by
    rw [lam]; exact Finset.sum_eq_zero fun i _ => by rw [hJe, he0 i, mul_zero]
  linarith

lemma GoodV.zero_eq {v : ℕ → ℚ} (hg : GoodV v) (h0 : v 0 ≠ 0) :
    ∃ a : ℕ, 0 < a ∧ v 0 = 1 / a := by
  rcases hg 0 with h | ⟨a, ha, hva⟩
  · exact absurd h h0
  · refine ⟨a, ha, ?_⟩
    rw [hva]; simp [denPN]

lemma exists_weights {v : ℕ → ℚ} {N : ℕ} (hnn : ∀ i, 0 ≤ v i) (hz : ∀ i, N ≤ i → v i = 0) :
    ∃ d : ℕ, 0 < d ∧ ∀ i, ∃ w : ℕ, (w : ℚ) = d * v i := by
  obtain ⟨d, w, hd, hw⟩ := Chart.exists_scale (e := fun i : Fin N => v i) (fun i => hnn i)
  refine ⟨d, hd, fun i => ?_⟩
  by_cases hi : i < N
  · exact ⟨w ⟨i, hi⟩, hw ⟨i, hi⟩⟩
  · exact ⟨0, by rw [hz i (by omega)]; simp⟩

end Facts

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing

/-- The real-points statement for the torsor (proved separately). -/
def TorsorRealPts : Prop :=
  ∀ {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] [IsNoetherianRing A]
    {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
    (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
    {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (_hd : 0 < d)
    (_hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)
    (_hπ0 : π ≠ 0) (_hk2 : v₀ 1 ≠ 0) (K : Set (RealPt A)), IsCompact K →
    ∃ K' : Set (RealPt (Torsor hI hmax h𝔭 d hπ)), IsCompact K' ∧
      IsMonotoneSurjOn (RealPt.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))) K' K

section TorsorSFD

variable {A : SmoothFactorialDomain} {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)

/-- The torsor as a smooth factorial domain. -/
abbrev torsorSFD (hk2 : v₀ 1 ≠ 0) (hπp : Prime π) (hπ𝔭 : π ∈ 𝔭) : SmoothFactorialDomain where
  carrier := Torsor hI hmax h𝔭 d hπ
  isDomain := torsor_isDomain hI hmax h𝔭 hπ hπp.ne_zero
  smooth := torsor_smooth hI hmax h𝔭 hd hw hπ
  ufd := torsor_ufd hI hmax h𝔭 hd hw hπ hk2 hπp hπ𝔭

end TorsorSFD

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing

set_option maxHeartbeats 1000000 in
/-- **The step of the algorithm.** -/
theorem stepProp (hRP : TorsorRealPts) (N : ℕ) : StepProp N := by
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
      div_dimOK hD, ?_⟩
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
    obtain ⟨K', hK', hmono⟩ := hRP hI hmax h𝔭 hd hw hπ hπp.ne_zero hk2 K hK
    set U := torsorSFD hI hmax h𝔭 hd hw hπ hk2 hπp hπ𝔭
    refine ⟨U, IsScalarTower.toAlgHom ℚ A (Torsor hI hmax h𝔭 d hπ), K',
      torsorI hI hmax h𝔭 hd hπ, torsorS hI hmax h𝔭 hπ ^ d, m + (nGen hI hmax h𝔭 d + 1),
      torsor_injective hI hmax h𝔭 hπ hπp.ne_zero, ?_, torsorI_ne_bot hI hmax h𝔭 hd hπ hπp.ne_zero,
      hK', hmono, torsor_vertOK hI hmax h𝔭 hd hw hπ hπp.ne_zero hV,
      torsor_dimOK hI hmax h𝔭 hd hw hπ hπp.ne_zero hD, ?_⟩
    · exact torsor_map_eq hI hmax h𝔭 hd hπ
    · exact hmeas (torsorI_ne_bot hI hmax h𝔭 hd hπ hπp.ne_zero)
        (torsor_vertOK hI hmax h𝔭 hd hw hπ hπp.ne_zero hV)
        (torsor_dimOK hI hmax h𝔭 hd hw hπ hπp.ne_zero hD)
        (by intro Q _ hQ v hv; exact torsor_inv_ge hI hmax h𝔭 hd hw hπ hπp.ne_zero Q hQ hv)
        (fun _ => torsor_count hI hmax h𝔭 hd hw hπ hπp.ne_zero)

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing

/-- **Principalization** (Proposition 4.6), assuming the real-points statement for torsors. -/
theorem principalizationExtension_of (hRP : TorsorRealPts) : PrincipalizationExtension := by
  intro A I K hI _ hK
  obtain ⟨𝔪₀, h𝔪₀⟩ := Ideal.exists_maximal A
  obtain ⟨N, ⟨c₀⟩⟩ := exists_chart_atPrime 𝔪₀
  have hV : VertOK I 0 := fun 𝔪 h𝔪 _ =>
    ⟨Fin.elim0, Fin.elim0, fun j => Fin.elim0 j, by
      rw [Matrix.det_isEmpty]; exact (Ideal.ne_top_iff_one _).1 h𝔪.ne_top⟩
  have hD : DimOK I 0 N := fun 𝔪 _ _ n ⟨c⟩ => by
    have := chart_card_eq_of_domain 𝔪 𝔪₀ c c₀
    omega
  exact princ_of_step N (stepProp hRP N) A I K 0 hI hK hV hD

end BezoutCounterexample.Principalization

