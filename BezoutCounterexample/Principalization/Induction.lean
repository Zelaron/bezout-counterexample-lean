import BezoutCounterexample.Principalization.Divisorial
import BezoutCounterexample.Mobius

/-!
# Ingredients of the principalization induction

Auxiliary invariant and real-point facts used in the principalization construction.
The induction in Proposition 4.6 is carried out in
`BezoutCounterexample/PrincipalizationStar.lean`.

* `MaxInv`, `measureW`, `measure_lt_of`: the maximal invariant and the termination measure
  `(encW N v₀, #components)` in a well-founded lexicographic order.
* `IsMonotoneSurjOn.comap_comp`, `IsMonotoneSurjOn.id'`: composition of monotone surjections of
  real points.
* `InvAt.goodV`, `InvAt.zero_ne`, `GoodV.zero_eq`, `exists_weights`: facts about invariants.
* `torsorSFD`: the torsor as a smooth factorial domain.
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
  have : CompactSpace K'' := isCompact_iff_compactSpace.1 hK''
  have heq : m.restrict (RealPt.comap (g.comp f)) K'' K =
      (m1.restrict (RealPt.comap f) K' K) ∘ (m2.restrict (RealPt.comap g) K'' K') := by
    funext z; rfl
  rw [heq]
  exact s1.comp s2

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

section Facts

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

omit [Algebra.Smooth ℚ A] in
lemma InvAt.goodV {I : Ideal A} (hI : I ≠ ⊥) {𝔪 : Ideal A} [𝔪.IsMaximal] (hI𝔪 : I ≤ 𝔪)
    {v : ℕ → ℚ} (hv : InvAt I 𝔪 v) : GoodV v := by
  obtain ⟨n, e, he, rfl⟩ := hv
  have : IsNoetherianRing (Localization.AtPrime 𝔪) :=
    IsLocalization.isNoetherianRing 𝔪.primeCompl _ inferInstance
  obtain ⟨J, -, -⟩ := he.1
  exact he.goodV (Iloc_ne_bot hI 𝔪) (Iloc_le hI𝔪) J.c J.centred

omit [IsNoetherianRing A] [Algebra.Smooth ℚ A] in
lemma InvAt.zero_ne {I : Ideal A} (hI : I ≠ ⊥) {𝔪 : Ideal A} [𝔪.IsMaximal]
    {v : ℕ → ℚ} (hv : InvAt I 𝔪 v) : v 0 ≠ 0 := by
  obtain ⟨n, e, he, rfl⟩ := hv
  intro h0
  have he0 : ∀ i, e i = 0 := by
    intro i
    have hi0 : (0 : ℕ) < n := by have := i.2; omega
    have h1 : e ⟨0, hi0⟩ = 0 := by simpa [ext0, dite_eq_left hi0] using h0
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
