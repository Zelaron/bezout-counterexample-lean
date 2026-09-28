import BezoutCounterexample.Principalization.Invariant

/-!
# The maximal locus and its components

Theorem 3.3 (3), (4) (`thm:invariant`) of the paper.

For a nonzero ideal `I` of a smooth `ℚ`-domain `A`:

* `InvAt`, `exists_invAt`, `invAt_semicont`: the invariant at points and its upper
  semicontinuity; `exists_maxInv`: the maximal invariant exists.
* `maxLocus`, `locusIdeal`, `LocData`: the locus of maximal invariant, its ideal and its local
  structure; `LocData.eq_p_of_minimal`,
  `minimalPrimes_sup_eq_top`: its components are the disjoint zero sets of the minimal primes.
* `cRF`, `compF`: the maximal centres and the filtration of a component;
  `compF_map`, `compF_map_of_not_le`: the filtration localizes to the maximal centres;
  `compF_one_div`, `pow_le_compF`.
-/

noncomputable section


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

/-- `I` extended to the local ring at `𝔪`. -/
abbrev Iloc (I : Ideal A) (𝔪 : Ideal A) [𝔪.IsPrime] : Ideal (Localization.AtPrime 𝔪) :=
  I.map (algebraMap A (Localization.AtPrime 𝔪))

omit [Algebra ℚ A] [Algebra.Smooth ℚ A] in
lemma Iloc_ne_bot {I : Ideal A} (hI : I ≠ ⊥) (𝔪 : Ideal A) [𝔪.IsPrime] : Iloc I 𝔪 ≠ ⊥ := by
  intro h
  apply hI
  rw [eq_bot_iff]
  intro a ha
  have : algebraMap A (Localization.AtPrime 𝔪) a = 0 := by
    rw [← Ideal.mem_bot, ← h]; exact Ideal.mem_map_of_mem _ ha
  rw [Ideal.mem_bot]
  exact (IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors 𝔪)) (by rw [this, map_zero])

omit [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] in
lemma Iloc_le {I : Ideal A} {𝔪 : Ideal A} [𝔪.IsPrime] (h : I ≤ 𝔪) :
    Iloc I 𝔪 ≤ maximalIdeal (Localization.AtPrime 𝔪) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪 a]
  exact h ha

omit [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] in
lemma le_of_Iloc_le {I : Ideal A} {𝔪 : Ideal A} [𝔪.IsPrime]
    (h : Iloc I 𝔪 ≤ maximalIdeal (Localization.AtPrime 𝔪)) : I ≤ 𝔪 := by
  intro a ha
  rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪 a]
  exact h (Ideal.mem_map_of_mem _ ha)

/-- `v` is the invariant of `I` at the point `𝔪`. -/
def InvAt (I : Ideal A) (𝔪 : Ideal A) [𝔪.IsPrime] (v : ℕ → ℚ) : Prop :=
  ∃ (n : ℕ) (e : Fin n → ℚ), IsInv (Iloc I 𝔪) n e ∧ ext0 e = v

lemma ext0_injective {n : ℕ} : Function.Injective (ext0 (n := n)) := by
  intro e e' h
  funext i
  have := congrFun h i
  rwa [ext0_apply, ext0_apply] at this

lemma ext0_le {n : ℕ} {e e' : Fin n → ℚ} (h : toLex e ≤ toLex e') : toLex (ext0 e) ≤ toLex (ext0 e') := by
  rcases h.lt_or_eq with h | h
  · obtain ⟨i, hbelow, hi⟩ := h
    refine le_of_lt ⟨i, fun j hj => ?_, ?_⟩
    · simp only [Pi.toLex_apply] at hbelow ⊢
      have hjn : j < n := lt_trans hj i.2
      have := hbelow ⟨j, hjn⟩ hj
      simp only [ext0, dite_eq_left hjn]; exact this
    · simp only [Pi.toLex_apply] at hi ⊢
      simp only [ext0, dite_eq_left i.2]; exact hi
  · rw [toLex.injective h]

lemma IsInv.card_eq {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] {I : Ideal S}
    {n n' : ℕ} {e : Fin n → ℚ} (he : IsInv I n e) (c' : Chart S n') : n = n' := by
  obtain ⟨⟨J, -, -⟩, -⟩ := he
  exact Chart.card_eq J.c c'

omit [IsDomain A] [Algebra.Smooth ℚ A] in
lemma InvAt.unique {I : Ideal A} {𝔪 : Ideal A} [𝔪.IsPrime] {v v' : ℕ → ℚ} (h : InvAt I 𝔪 v)
    (h' : InvAt I 𝔪 v') : v = v' := by
  obtain ⟨n, e, he, rfl⟩ := h
  obtain ⟨n', e', he', rfl⟩ := h'
  have hc : n = n' := by obtain ⟨⟨J', -, -⟩, -⟩ := he'; exact he.card_eq J'.c
  subst hc
  rw [he.unique he']

variable [IsNoetherianRing A]

omit [IsNoetherianRing A] in
/-- **Local structure of the invariant**, repackaged: the invariant at `𝔪` is computed by the
transported chart and bounds the invariants at all points of a neighbourhood. -/
theorem local_inv (I : Ideal A) (hI : I ≠ ⊥) (𝔪 : Ideal A) [𝔪.IsMaximal] (hI𝔪 : I ≤ 𝔪) :
    ∃ (n : ℕ) (M' : Submonoid A) (g : A) (hg : g ∉ 𝔪) (hctrl : Loc.Ctrl M' g)
      (k : ℕ) (ck : Chart (Localization M') n) (ek : Fin n → ℚ),
      (∀ i, ek i ≠ 0 ↔ (i : ℕ) < k) ∧ I.map (algebraMap A (Localization M')) ≤ ck.RF ek 1 ∧
      IsInv (Iloc I 𝔪) n ek ∧ (Loc.transport (hctrl 𝔪 hg) ck).IsCentred ∧
      ∀ (𝔪' : Ideal A) [𝔪'.IsMaximal] (hg' : g ∉ 𝔪'),
        ∀ J' : MC (Localization.AtPrime 𝔪') n, J'.Adm (Iloc I 𝔪') →
          toLex ek ≤ toLex J'.e ∧
          (J'.e = ek → ∀ t, J'.RF t = (Loc.transport (hctrl 𝔪' hg') ck).RF ek t) := by
  obtain ⟨n, M', g, hg, hctrl, k, ck, ek, hsupp, hnn, hanti, hadm, hM', hcent, hbound⟩ :=
    local_structure I hI 𝔪 hI𝔪
  refine ⟨n, M', g, hg, hctrl, k, ck, ek, hsupp, hadm, ⟨⟨⟨_, ek, hcent, hnn, hanti⟩, ?_, rfl⟩,
    fun J' hJ' => (hbound 𝔪 hg J' hJ').1⟩, hcent, hbound⟩
  have h1 := Ideal.map_mono (f := Loc.map hM') hadm
  rw [Loc.map_map_algebraMap, Loc.map_RF] at h1
  exact h1

omit [IsNoetherianRing A] in
lemma exists_invAt {I : Ideal A} (hI : I ≠ ⊥) (𝔪 : Ideal A) [𝔪.IsMaximal] (hI𝔪 : I ≤ 𝔪) :
    ∃ v, InvAt I 𝔪 v := by
  obtain ⟨n, -, -, -, -, -, -, ek, -, -, hinv, -⟩ := local_inv I hI 𝔪 hI𝔪
  exact ⟨_, n, ek, hinv, rfl⟩

omit [IsNoetherianRing A] in
/-- **Upper semicontinuity of the invariant.** -/
lemma invAt_semicont {I : Ideal A} (hI : I ≠ ⊥) (𝔪 : Ideal A) [𝔪.IsMaximal] (hI𝔪 : I ≤ 𝔪)
    {v : ℕ → ℚ} (hv : InvAt I 𝔪 v) :
    ∃ g : A, g ∉ 𝔪 ∧ ∀ (𝔪' : Ideal A) [𝔪'.IsMaximal], g ∉ 𝔪' → ∀ v', InvAt I 𝔪' v' →
      toLex v ≤ toLex v' := by
  obtain ⟨n, M', g, hg, hctrl, k, ck, ek, hsupp, hadm, hinv, hcent, hbound⟩ := local_inv I hI 𝔪 hI𝔪
  obtain rfl : v = ext0 ek := hv.unique ⟨n, ek, hinv, rfl⟩
  refine ⟨g, hg, fun 𝔪' _ hg' v' hv' => ?_⟩
  obtain ⟨n', e', he', rfl⟩ := hv'
  obtain rfl := he'.card_eq (Loc.transport (hctrl 𝔪' hg') ck)
  obtain ⟨⟨J', hJ', hJ'e⟩, -⟩ := he'
  have := (hbound 𝔪' hg' J' hJ').1
  rw [hJ'e] at this
  exact ext0_le this

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

omit [IsNoetherianRing A] in
/-- **The maximal invariant exists** (upper semicontinuity and quasi-compactness). -/
theorem exists_maxInv {I : Ideal A} (hI : I ≠ ⊥) (hItop : I ≠ ⊤) :
    ∃ v₀ : ℕ → ℚ, (∃ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal), I ≤ 𝔪 ∧ InvAt I 𝔪 v₀) ∧
      ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v := by
  classical
  set S := {𝔪 : Ideal A // 𝔪.IsMaximal ∧ I ≤ 𝔪}
  have hv : ∀ p : S, ∃ v, haveI := p.2.1; InvAt I p.1 v := fun p => by
    have := p.2.1; exact exists_invAt hI p.1 p.2.2
  choose v hvv using hv
  have hg : ∀ p : S, ∃ g : A, g ∉ p.1 ∧ ∀ (𝔪' : Ideal A) [𝔪'.IsMaximal], g ∉ 𝔪' →
      ∀ v', InvAt I 𝔪' v' → toLex (v p) ≤ toLex v' := fun p => by
    have := p.2.1; exact invAt_semicont hI p.1 p.2.2 (hvv p)
  choose g hgm hgv using hg
  have htop : I ⊔ Ideal.span (Set.range g) = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    have hp : (⟨𝔪, h𝔪, le_sup_left.trans hle⟩ : S).1 = 𝔪 := rfl
    exact hgm ⟨𝔪, h𝔪, le_sup_left.trans hle⟩
      (hle (le_sup_right (a := I) (Ideal.subset_span ⟨_, rfl⟩)))
  have h1 : (1 : A) ∈ I ⊔ Ideal.span (Set.range g) := by rw [htop]; trivial
  obtain ⟨i, hi, y, hy, hiy⟩ := Submodule.mem_sup.1 h1
  obtain ⟨f, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hy
  have hF : f.support.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finsupp.support_eq_empty] at h
    subst h
    simp only [Finsupp.sum_zero_index, add_zero] at hiy
    exact hItop ((Ideal.eq_top_iff_one I).2 (hiy ▸ hi))
  obtain ⟨p₀, hp₀, hmin⟩ := Finset.exists_min_image f.support (fun p => toLex (v p)) hF
  refine ⟨v p₀, ⟨p₀.1, p₀.2.1, p₀.2.2, by have := p₀.2.1; exact hvv p₀⟩, fun 𝔪 _ hI𝔪 w hw => ?_⟩
  -- some `g p` with `p ∈ F` avoids `𝔪`
  obtain ⟨p, hp, hp𝔪⟩ : ∃ p ∈ f.support, g p ∉ 𝔪 := by
    by_contra h
    push Not at h
    have : (1 : A) ∈ 𝔪 := by
      rw [← hiy]
      refine Ideal.add_mem _ (hI𝔪 hi) ?_
      rw [Finsupp.sum]
      exact Ideal.sum_mem _ fun p hp => Ideal.mul_mem_left _ _ (h p hp)
    exact (Ideal.IsMaximal.ne_top ‹_›) ((Ideal.eq_top_iff_one _).2 this)
  exact (hmin p hp).trans (hgv p 𝔪 hp𝔪 w hw)

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

/-- **Local structure of the maximal locus.** Near a point `𝔪` of maximal invariant `v₀`, the
points of maximal invariant are exactly the zeros of the first `k` coordinates of a chart, and the
maximal centres there are given by the chart. -/
theorem maxLocus_local {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
    (𝔪 : Ideal A) [𝔪.IsMaximal] (hI𝔪 : I ≤ 𝔪) (h𝔪 : InvAt I 𝔪 v₀) :
    ∃ (n : ℕ) (M' : Submonoid A) (g : A) (hg : g ∉ 𝔪) (hctrl : Loc.Ctrl M' g) (k : ℕ)
      (ck : Chart (Localization M') n) (ek : Fin n → ℚ),
      (∀ i, ek i ≠ 0 ↔ (i : ℕ) < k) ∧ ext0 ek = v₀ ∧
      I.map (algebraMap A (Localization M')) ≤ ck.RF ek 1 ∧
      IsInv (Iloc I 𝔪) n ek ∧ (Loc.transport (hctrl 𝔪 hg) ck).IsCentred ∧
      ∀ (𝔪' : Ideal A) [𝔪'.IsMaximal] (hg' : g ∉ 𝔪'),
        ((I ≤ 𝔪' ∧ InvAt I 𝔪' v₀) ↔ ∀ i : Fin n, (i : ℕ) < k →
          (Loc.transport (hctrl 𝔪' hg') ck).x i ∈ maximalIdeal (Localization.AtPrime 𝔪')) ∧
        ∀ J' : MC (Localization.AtPrime 𝔪') n, J'.Adm (Iloc I 𝔪') → J'.e = ek →
          ∀ t, J'.RF t = (Loc.transport (hctrl 𝔪' hg') ck).RF ek t := by
  obtain ⟨n, M', g, hg, hctrl, k, ck, ek, hsupp, hadm, hinv, hcent, hbound⟩ := local_inv I hI 𝔪 hI𝔪
  have hv₀ : ext0 ek = v₀ := (InvAt.unique ⟨n, ek, hinv, rfl⟩ h𝔪)
  refine ⟨n, M', g, hg, hctrl, k, ck, ek, hsupp, hv₀, hadm, hinv, hcent,
    fun 𝔪' _ hg' => ⟨⟨?_, ?_⟩, fun J' hJ' he => (hbound 𝔪' hg' J' hJ').2 he⟩⟩
  · rintro ⟨-, n', e', he', hev⟩
    obtain rfl := he'.card_eq (Loc.transport (hctrl 𝔪' hg') ck)
    have hee : e' = ek := ext0_injective (hev.trans hv₀.symm)
    subst e'
    obtain ⟨⟨J', hJ', hJ'e⟩, -⟩ := he'
    have hRF := (hbound 𝔪' hg' J' hJ').2 hJ'e
    intro i hi
    have hpos : 0 < J'.e i := by
      rw [hJ'e]; exact lt_of_le_of_ne (hinv.nonneg i) (Ne.symm ((hsupp i).2 hi))
    have hmem := (Loc.transport (hctrl 𝔪' hg') ck).x_mem_RF ek i ((hsupp i).2 hi)
    rw [← hRF, ← hJ'e] at hmem
    exact J'.centred.RF_le_maximalIdeal hpos hmem
  · intro hx
    have := residueField_isIntegral 𝔪'
    set c₁ := Loc.transport (hctrl 𝔪' hg') ck
    obtain ⟨c'', hc'', hxx⟩ := Chart.exists_centred c₁
    have hRF : ∀ t, c''.RF ek t = c₁.RF ek t := fun t =>
      Chart.RF_congr (fun i hi => hxx i (hx i ((hsupp i).1 hi))) t
    have hadm' : Iloc I 𝔪' ≤ c''.RF ek 1 := by
      rw [hRF]
      have h1 := Ideal.map_mono (f := Loc.map (hctrl 𝔪' hg')) hadm
      rw [Loc.map_map_algebraMap, Loc.map_RF] at h1
      exact h1
    set J'' : MC (Localization.AtPrime 𝔪') n := ⟨c'', ek, hc'', hinv.nonneg, hinv.anti⟩
    have hIS : IsInv (Iloc I 𝔪') n ek :=
      ⟨⟨J'', hadm', rfl⟩, fun J' hJ' => (hbound 𝔪' hg' J' hJ').1⟩
    refine ⟨le_of_Iloc_le (hadm'.trans (hc''.RF_le_maximalIdeal one_pos)), n, ek, hIS, hv₀⟩

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

/-- The locus of points of `V(I)` where the invariant is `v₀`. -/
def maxLocus (I : Ideal A) (v₀ : ℕ → ℚ) : Set (Ideal A) :=
  {𝔪 | ∃ _ : 𝔪.IsMaximal, I ≤ 𝔪 ∧ InvAt I 𝔪 v₀}

/-- The ideal of the locus of maximal invariant. -/
def locusIdeal (I : Ideal A) (v₀ : ℕ → ℚ) : Ideal A := sInf (maxLocus I v₀)

omit [IsDomain A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
lemma mem_locusIdeal {I : Ideal A} {v₀ : ℕ → ℚ} {f : A} :
    f ∈ locusIdeal I v₀ ↔ ∀ 𝔪 ∈ maxLocus I v₀, f ∈ 𝔪 := Submodule.mem_sInf

omit [IsNoetherianRing A] in
/-- The maximal locus is closed: a maximal ideal containing its ideal lies in it. -/
theorem mem_maxLocus_of_le {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
    (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
    (𝔪 : Ideal A) [h𝔪 : 𝔪.IsMaximal] (hle : locusIdeal I v₀ ≤ 𝔪) : 𝔪 ∈ maxLocus I v₀ := by
  by_contra hZ
  by_cases hI𝔪 : I ≤ 𝔪
  · obtain ⟨v, hv⟩ := exists_invAt hI 𝔪 hI𝔪
    have hne : v ≠ v₀ := fun h => hZ ⟨h𝔪, hI𝔪, h ▸ hv⟩
    have hlt : toLex v₀ < toLex v := lt_of_le_of_ne (hmax 𝔪 hI𝔪 v hv)
      (fun h => hne (toLex.injective h).symm)
    obtain ⟨g, hg, hgv⟩ := invAt_semicont hI 𝔪 hI𝔪 hv
    apply hg
    apply hle
    rw [mem_locusIdeal]
    rintro 𝔪' ⟨h𝔪', hI', hv'⟩
    by_contra hg'
    exact absurd (hgv 𝔪' hg' v₀ hv') (not_le.2 hlt)
  · obtain ⟨f, hf, hf𝔪⟩ := Set.not_subset.1 hI𝔪
    apply hf𝔪
    apply hle
    rw [mem_locusIdeal]
    rintro 𝔪' ⟨-, hI', -⟩
    exact hI' hf

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

/-- Local data of the maximal locus at a point `𝔪` (see `maxLocus_local`). -/
structure LocData (I : Ideal A) (v₀ : ℕ → ℚ) (𝔪 : Ideal A) [𝔪.IsMaximal] where
  n : ℕ
  M : Submonoid A
  g : A
  hg : g ∉ 𝔪
  ctrl : Loc.Ctrl M g
  k : ℕ
  ck : Chart (Localization M) n
  ek : Fin n → ℚ
  supp : ∀ i, ek i ≠ 0 ↔ (i : ℕ) < k
  hv : ext0 ek = v₀
  adm : I.map (algebraMap A (Localization M)) ≤ ck.RF ek 1
  inv : IsInv (Iloc I 𝔪) n ek
  cent : (Loc.transport (ctrl 𝔪 hg) ck).IsCentred
  iff : ∀ (𝔪' : Ideal A) [𝔪'.IsMaximal] (hg' : g ∉ 𝔪'),
    ((I ≤ 𝔪' ∧ InvAt I 𝔪' v₀) ↔ ∀ i : Fin n, (i : ℕ) < k →
      (Loc.transport (ctrl 𝔪' hg') ck).x i ∈ maximalIdeal (Localization.AtPrime 𝔪'))
  rf : ∀ (𝔪' : Ideal A) [𝔪'.IsMaximal] (hg' : g ∉ 𝔪'),
    ∀ J' : MC (Localization.AtPrime 𝔪') n, J'.Adm (Iloc I 𝔪') → J'.e = ek →
      ∀ t, J'.RF t = (Loc.transport (ctrl 𝔪' hg') ck).RF ek t

lemma LocData.nonempty {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ} (𝔪 : Ideal A) [𝔪.IsMaximal]
    (hI𝔪 : I ≤ 𝔪) (h𝔪 : InvAt I 𝔪 v₀) : Nonempty (LocData I v₀ 𝔪) := by
  obtain ⟨n, M, g, hg, ctrl, k, ck, ek, supp, hv, adm, inv, cent, h⟩ :=
    maxLocus_local hI 𝔪 hI𝔪 h𝔪
  exact ⟨⟨n, M, g, hg, ctrl, k, ck, ek, supp, hv, adm, inv, cent, fun 𝔪' _ hg' => (h 𝔪' hg').1,
    fun 𝔪' _ hg' => (h 𝔪' hg').2⟩⟩

namespace LocData

variable {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪)

/-- The ideal of the maximal locus at `𝔪`, in `A_𝔪`. -/
def P : Ideal (Localization.AtPrime 𝔪) :=
  Ideal.span ((Loc.transport (D.ctrl 𝔪 D.hg) D.ck).x '' {i | (i : ℕ) < D.k})

/-- The corresponding prime of `A`. -/
def p : Ideal A := D.P.under A

instance : D.P.IsPrime := Chart.IsCentred.span_x_isPrime _ D.cent D.k

instance : D.p.IsPrime := Ideal.comap_isPrime _ _

omit [Algebra.Smooth ℚ A] [IsNoetherianRing A] [IsDomain A] in
lemma P_le_max : D.P ≤ maximalIdeal (Localization.AtPrime 𝔪) := by
  rw [P, Ideal.span_le]
  rintro _ ⟨i, -, rfl⟩
  exact D.cent.x_mem i

omit [Algebra.Smooth ℚ A] [IsNoetherianRing A] [IsDomain A] in
lemma p_le : D.p ≤ 𝔪 := by
  intro a ha
  rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪 a]
  exact D.P_le_max ha

omit [Algebra.Smooth ℚ A] [IsNoetherianRing A] [IsDomain A] in
lemma map_p : D.p.map (algebraMap A (Localization.AtPrime 𝔪)) = D.P :=
  IsLocalization.map_under (M := 𝔪.primeCompl) (S := Localization.AtPrime 𝔪) D.P

omit [Algebra.Smooth ℚ A] [IsNoetherianRing A] [IsDomain A] in
/-- Numerators of the chart functions. -/
lemma exists_num (i : Fin D.n) : ∃ (a : A) (m : D.M),
    D.ck.x i = IsLocalization.mk' (Localization D.M) a m := by
  obtain ⟨⟨a, m⟩, h⟩ := IsLocalization.mk'_surjective D.M (D.ck.x i)
  exact ⟨a, m, h.symm⟩

omit [Algebra.Smooth ℚ A] [IsNoetherianRing A] [IsDomain A] in
lemma transport_x_mk' {N : Submonoid A} (h : D.M ≤ N) (i : Fin D.n) (a : A) (m : D.M)
    (hx : D.ck.x i = IsLocalization.mk' (Localization D.M) a m) :
    (Loc.transport h D.ck).x i = IsLocalization.mk' (Localization N) a ⟨m, h m.2⟩ := by
  rw [Loc.transport_x, hx, Loc.map_mk']

omit [Algebra.Smooth ℚ A] [IsNoetherianRing A] [IsDomain A] in
/-- The numerators of the first `k` chart functions lie in `𝔭`. -/
lemma num_mem_p (i : Fin D.n) (hi : (i : ℕ) < D.k) (a : A) (m : D.M)
    (hx : D.ck.x i = IsLocalization.mk' (Localization D.M) a m) : a ∈ D.p := by
  show algebraMap A _ a ∈ D.P
  have h1 : (Loc.transport (D.ctrl 𝔪 D.hg) D.ck).x i ∈ D.P := Ideal.subset_span ⟨i, hi, rfl⟩
  rw [D.transport_x_mk' _ i a m hx] at h1
  have h2 := D.P.mul_mem_right (algebraMap A (Localization.AtPrime 𝔪) m) h1
  rwa [IsLocalization.mk'_spec] at h2

omit [Algebra.Smooth ℚ A] [IsNoetherianRing A] [IsDomain A] in
/-- Conversely, the points of `V(𝔭) ∩ D(g)` are in the maximal locus. -/
lemma mem_of_p_le (𝔪' : Ideal A) [𝔪'.IsMaximal] (hg' : D.g ∉ 𝔪') (hp : D.p ≤ 𝔪') :
    I ≤ 𝔪' ∧ InvAt I 𝔪' v₀ := by
  rw [D.iff 𝔪' hg']
  intro i hi
  obtain ⟨a, m, hx⟩ := D.exists_num i
  rw [D.transport_x_mk' _ i a m hx,
    IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime 𝔪') 𝔪']
  exact hp (D.num_mem_p i hi a m hx)

omit [Algebra.Smooth ℚ A] [IsNoetherianRing A] [IsDomain A] in
/-- `g aᵢ` lies in the ideal of the maximal locus. -/
lemma g_mul_num_mem (i : Fin D.n) (hi : (i : ℕ) < D.k) (a : A) (m : D.M)
    (hx : D.ck.x i = IsLocalization.mk' (Localization D.M) a m) :
    D.g * a ∈ locusIdeal I v₀ := by
  rw [mem_locusIdeal]
  rintro 𝔪'' ⟨h𝔪'', hI'', hv''⟩
  by_cases hg'' : D.g ∈ 𝔪''
  · exact Ideal.mul_mem_right _ _ hg''
  · refine Ideal.mul_mem_left _ _ ?_
    have := (D.iff 𝔪'' hg'').1 ⟨hI'', hv''⟩ i hi
    rw [D.transport_x_mk' _ i a m hx,
      IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime 𝔪'') 𝔪''] at this
    exact this

omit [Algebra.Smooth ℚ A] [IsNoetherianRing A] [IsDomain A] in
/-- The chart functions lie in the extension of the ideal of the locus. -/
lemma P_le_map {𝔮 : Ideal A} (h𝔮 : locusIdeal I v₀ ≤ 𝔮) :
    D.P ≤ 𝔮.map (algebraMap A (Localization.AtPrime 𝔪)) := by
  rw [P, Ideal.span_le]
  rintro _ ⟨i, hi, rfl⟩
  obtain ⟨a, m, hx⟩ := D.exists_num i
  rw [SetLike.mem_coe, D.transport_x_mk' _ i a m hx,
    IsLocalization.mk'_mem_map_algebraMap_iff 𝔪.primeCompl]
  exact ⟨D.g, D.hg, h𝔮 (D.g_mul_num_mem i hi a m hx)⟩

end LocData

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

omit [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
lemma under_map_atPrime {𝔪 : Ideal A} [𝔪.IsPrime] {𝔮 : Ideal A} [h𝔮 : 𝔮.IsPrime] (h𝔮𝔪 : 𝔮 ≤ 𝔪) :
    (𝔮.map (algebraMap A (Localization.AtPrime 𝔪))).under A = 𝔮 := by
  refine IsLocalization.under_map_of_isPrime_disjoint 𝔪.primeCompl _ h𝔮 ?_
  rw [Set.disjoint_left]
  intro a ha haq
  exact ha (h𝔮𝔪 haq)

namespace LocData

variable {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪)

omit [IsDomain A] in
/-- The ideal of the maximal locus is contained in `𝔭` (Nullstellensatz). -/
theorem locusIdeal_le_p : locusIdeal I v₀ ≤ D.p := by
  intro f hf
  by_contra hfp
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℚ)
  have hgf : D.g * f ∈ D.p := by
    have hj : D.p.jacobson = D.p := IsJacobsonRing.out inferInstance (inferInstance : D.p.IsPrime).isRadical
    rw [← hj, Ideal.jacobson, Ideal.mem_sInf]
    rintro 𝔪' ⟨hp𝔪', h𝔪'⟩
    have := h𝔪'
    by_cases hg' : D.g ∈ 𝔪'
    · exact Ideal.mul_mem_right _ _ hg'
    · obtain ⟨hI', hv'⟩ := D.mem_of_p_le 𝔪' hg' hp𝔪'
      exact Ideal.mul_mem_left _ _ ((mem_locusIdeal.1 hf) 𝔪' ⟨h𝔪', hI', hv'⟩)
  rcases (inferInstance : D.p.IsPrime).mem_or_mem hgf with h | h
  · exact D.hg (D.p_le h)
  · exact hfp h

omit [IsDomain A] in
/-- `𝔭` is the only minimal prime of the ideal of the maximal locus contained in `𝔪`. -/
theorem eq_p_of_minimal {𝔮 : Ideal A} (h𝔮 : 𝔮 ∈ (locusIdeal I v₀).minimalPrimes)
    (h𝔮𝔪 : 𝔮 ≤ 𝔪) : 𝔮 = D.p := by
  have := h𝔮.1.1
  have hp : D.p ≤ 𝔮 := by
    intro a ha
    have h1 := D.P_le_map h𝔮.1.2 ha
    rw [← under_map_atPrime h𝔮𝔪]
    exact h1
  exact le_antisymm (h𝔮.2 ⟨inferInstance, D.locusIdeal_le_p⟩ hp) hp

end LocData

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
include hI hmax

omit [IsNoetherianRing A] in
/-- The points above a minimal prime of the ideal of the maximal locus lie in the locus. -/
theorem mem_maxLocus_of_minimal {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes)
    (𝔪 : Ideal A) [𝔪.IsMaximal] (h𝔭𝔪 : 𝔭 ≤ 𝔪) : I ≤ 𝔪 ∧ InvAt I 𝔪 v₀ := by
  obtain ⟨_, hI𝔪, hv⟩ := mem_maxLocus_of_le hI hmax 𝔪 (h𝔭.1.2.trans h𝔭𝔪)
  exact ⟨hI𝔪, hv⟩

/-- **Components of the maximal locus are disjoint.** -/
theorem minimalPrimes_sup_eq_top {𝔭 𝔭' : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes)
    (h𝔭' : 𝔭' ∈ (locusIdeal I v₀).minimalPrimes) (hne : 𝔭 ≠ 𝔭') : 𝔭 ⊔ 𝔭' = ⊤ := by
  by_contra htop
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ htop
  have := h𝔪
  obtain ⟨hI𝔪, hv⟩ := mem_maxLocus_of_minimal hI hmax h𝔭 𝔪 (le_sup_left.trans hle)
  obtain ⟨D⟩ := LocData.nonempty hI 𝔪 hI𝔪 hv
  exact hne ((D.eq_p_of_minimal h𝔭 (le_sup_left.trans hle)).trans
    (D.eq_p_of_minimal h𝔭' (le_sup_right.trans hle)).symm)

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

/-- The weighted ideals of the maximal admissible centre of `I` at `𝔪`. -/
def cRF (I : Ideal A) (𝔪 : Ideal A) [𝔪.IsPrime] (t : ℚ) : Ideal (Localization.AtPrime 𝔪) :=
  ⨅ (n : ℕ) (J : MC (Localization.AtPrime 𝔪) n) (_ : J.Adm (Iloc I 𝔪))
    (_ : IsInv (Iloc I 𝔪) n J.e), J.RF t

omit [Algebra.Smooth ℚ A] in
lemma cRF_eq {I : Ideal A} (hI : I ≠ ⊥) {𝔪 : Ideal A} [𝔪.IsMaximal] (hI𝔪 : I ≤ 𝔪) {n : ℕ}
    {J : MC (Localization.AtPrime 𝔪) n} (hJ : J.Adm (Iloc I 𝔪)) (hJi : IsInv (Iloc I 𝔪) n J.e)
    (t : ℚ) : cRF I 𝔪 t = J.RF t := by
  refine le_antisymm (iInf_le_of_le n (iInf_le_of_le J (iInf_le_of_le hJ (iInf_le _ hJi)))) ?_
  refine le_iInf fun n' => le_iInf fun J' => le_iInf fun hJ' => le_iInf fun hJi' => ?_
  obtain rfl := hJi.card_eq J'.c
  obtain ⟨J₀, hJ₀, hmax⟩ := MC.exists_max (Iloc_ne_bot hI 𝔪) (Iloc_le hI𝔪) J.c J.centred
  have hJ₀i : IsInv (Iloc I 𝔪) n J₀.e := ⟨⟨J₀, hJ₀, rfl⟩, fun J'' hJ'' => (hmax J'' hJ'').1⟩
  have h1 : J.e = J₀.e := hJi.unique hJ₀i
  have h2 : J'.e = J₀.e := hJi'.unique hJ₀i
  rw [(hmax J hJ).2 h1 t, (hmax J' hJ').2 h2 t]

omit [Algebra.Smooth ℚ A] in
lemma cRF_mul_le {I : Ideal A} (hI : I ≠ ⊥) {𝔪 : Ideal A} [𝔪.IsMaximal] (hI𝔪 : I ≤ 𝔪)
    {v : ℕ → ℚ} (hv : InvAt I 𝔪 v) (s t : ℚ) : cRF I 𝔪 s * cRF I 𝔪 t ≤ cRF I 𝔪 (s + t) := by
  obtain ⟨n, e, ⟨⟨J, hJ, rfl⟩, hmin⟩, -⟩ := hv
  have hJi : IsInv (Iloc I 𝔪) n J.e := ⟨⟨J, hJ, rfl⟩, hmin⟩
  rw [cRF_eq hI hI𝔪 hJ hJi, cRF_eq hI hI𝔪 hJ hJi, cRF_eq hI hI𝔪 hJ hJi]
  exact J.c.RF_mul_le J.e s t

omit [Algebra.Smooth ℚ A] in
lemma cRF_of_nonpos {I : Ideal A} (hI : I ≠ ⊥) {𝔪 : Ideal A} [𝔪.IsMaximal] (hI𝔪 : I ≤ 𝔪)
    {v : ℕ → ℚ} (hv : InvAt I 𝔪 v) {t : ℚ} (ht : t ≤ 0) : cRF I 𝔪 t = ⊤ := by
  obtain ⟨n, e, ⟨⟨J, hJ, rfl⟩, hmin⟩, -⟩ := hv
  rw [cRF_eq hI hI𝔪 hJ ⟨⟨J, hJ, rfl⟩, hmin⟩]
  exact J.c.RF_of_nonpos J.nonneg ht

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

namespace Loc

omit [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
lemma Ctrl.dvd_pow {M : Submonoid A} {g : A} (h : Ctrl M g) (m : A) (hm : m ∈ M) :
    ∃ b : ℕ, m ∣ g ^ b := by
  have hrad : g ∈ (Ideal.span {m}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hmP, hP⟩
    by_contra hg
    exact (h P hg hm) (hmP (Ideal.mem_span_singleton_self m))
  obtain ⟨b, hb⟩ := hrad
  exact ⟨b, Ideal.mem_span_singleton.1 hb⟩

omit [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
lemma Ctrl.sup {M : Submonoid A} {g : A} (h : Ctrl M g) : Ctrl (M ⊔ Submonoid.powers g) g := by
  intro P _ hg
  exact sup_le (h P hg) ((Submonoid.powers_le).2 hg)

omit [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
/-- A controlled localization is the localization away from the controlling element. -/
lemma away_of_ctrl {M : Submonoid A} {g : A} (h : Ctrl M g) :
    IsLocalization.Away g (Localization (M ⊔ Submonoid.powers g)) := by
  show IsLocalization (Submonoid.powers g) _
  rw [IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers g) (M ⊔ Submonoid.powers g)
    le_sup_right]
  · exact Localization.isLocalization
  · intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submonoid.mem_sup.1 hx
    obtain ⟨b, hb⟩ := h.dvd_pow y hy
    obtain ⟨a, rfl⟩ := hz
    exact ⟨g ^ b * g ^ a, ⟨b + a, by simp [pow_add]⟩, mul_dvd_mul hb dvd_rfl⟩

end Loc

namespace LocData

variable {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪)

/-- The controlled submonoid `M ⊔ gᴺ`. -/
abbrev N : Submonoid A := D.M ⊔ Submonoid.powers D.g

/-- The basic open `D(g)` as a ring. -/
abbrev B := Localization D.N

omit [Algebra.Smooth ℚ A] [IsNoetherianRing A] [IsDomain A] in
lemma ctrlN : Loc.Ctrl D.N D.g := D.ctrl.sup

instance away : IsLocalization.Away D.g D.B := Loc.away_of_ctrl D.ctrl

/-- The chart over `D(g)`. -/
def cB : Chart D.B D.n := Loc.transport le_sup_left D.ck

omit [Algebra.Smooth ℚ A] [IsNoetherianRing A] [IsDomain A] in
lemma transport_cB {𝔪' : Ideal A} [𝔪'.IsMaximal] (hg' : D.g ∉ 𝔪') :
    Loc.transport (D.ctrlN 𝔪' hg') D.cB = Loc.transport (D.ctrl 𝔪' hg') D.ck := by
  rw [cB, Loc.transport_trans]

/-- The weighted ideals over `D(g)`. -/
def RFB (t : ℚ) : Ideal D.B := D.cB.RF D.ek t

variable (hI : I ≠ ⊥)
include hI

omit [Algebra.Smooth ℚ A] in
/-- At points of the maximal locus in `D(g)`, the chart ideals are the maximal centre. -/
lemma RFB_map_of_mem {𝔪' : Ideal A} [𝔪'.IsMaximal] (hg' : D.g ∉ 𝔪') (hI' : I ≤ 𝔪')
    (hv' : InvAt I 𝔪' v₀) (t : ℚ) :
    (D.RFB t).map (Loc.map (D.ctrlN 𝔪' hg')) = cRF I 𝔪' t := by
  obtain ⟨n', e', he', hev⟩ := hv'
  obtain rfl := he'.card_eq (Loc.transport (D.ctrl 𝔪' hg') D.ck)
  have hee : e' = D.ek := ext0_injective (hev.trans D.hv.symm)
  subst hee
  obtain ⟨⟨J', hJ', hJ'e⟩, hmin⟩ := he'
  have hJi : IsInv (Iloc I 𝔪') D.n J'.e := ⟨⟨J', hJ', rfl⟩, by rw [hJ'e]; exact hmin⟩
  rw [cRF_eq hI hI' hJ' hJi, D.rf 𝔪' hg' J' hJ' hJ'e, RFB, Loc.map_RF, D.transport_cB hg']

omit hI [Algebra.Smooth ℚ A] [IsNoetherianRing A] [IsDomain A] in
/-- At other points of `D(g)` the chart ideals are trivial. -/
lemma RFB_map_of_not_mem {𝔪' : Ideal A} [𝔪'.IsMaximal] (hg' : D.g ∉ 𝔪')
    (hZ : ¬ (I ≤ 𝔪' ∧ InvAt I 𝔪' v₀)) (t : ℚ) :
    (D.RFB t).map (Loc.map (D.ctrlN 𝔪' hg')) = ⊤ := by
  rw [D.iff 𝔪' hg'] at hZ
  push Not at hZ
  obtain ⟨i, hi, hx⟩ := hZ
  set c₁ := Loc.transport (D.ctrl 𝔪' hg') D.ck
  have hunit : IsUnit (c₁.x i) := by
    rwa [← IsLocalRing.notMem_maximalIdeal]
  have hpos : 0 < D.ek i := lt_of_le_of_ne (D.inv.nonneg i) (Ne.symm ((D.supp i).2 hi))
  obtain ⟨N, hN⟩ := exists_nat_ge (t / D.ek i)
  have hmem : c₁.x i ^ N ∈ c₁.RF D.ek t := by
    have h1 := c₁.pow_mem_RF D.ek (c₁.x_mem_RF D.ek i ((D.supp i).2 hi)) N
    refine c₁.RF_antitone D.ek ?_ h1
    rw [div_le_iff₀ hpos] at hN
    exact hN
  rw [RFB, Loc.map_RF, D.transport_cB hg']
  exact Ideal.eq_top_of_isUnit_mem _ hmem (hunit.pow N)

end LocData

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

namespace LocData

variable {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪)

omit [Algebra.Smooth ℚ A] [IsNoetherianRing A] [IsDomain A] in
lemma map_algebraMap_B {𝔪' : Ideal A} [𝔪'.IsMaximal] (hg' : D.g ∉ 𝔪') (x : A) :
    Loc.map (D.ctrlN 𝔪' hg') (algebraMap A D.B x) = algebraMap A (Localization.AtPrime 𝔪') x :=
  Loc.map_algebraMap _ x

omit [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
/-- Pulling membership back from a point of `D(g)` to `D(g)`. -/
lemma exists_of_mem_map {𝔪' : Ideal A} [𝔪'.IsMaximal] (hg' : D.g ∉ 𝔪') (J : Ideal D.B) {x : A}
    (hx : algebraMap A (Localization.AtPrime 𝔪') x ∈ J.map (Loc.map (D.ctrlN 𝔪' hg'))) :
    ∃ y : A, y ∉ 𝔪' ∧ algebraMap A D.B (y * x) ∈ J := by
  have hN' := D.ctrlN 𝔪' hg'
  let := Loc.alg hN'
  have := Loc.tower hN'
  have := Loc.isLoc hN'
  have halg : ∀ y : D.B, Loc.map hN' y = algebraMap D.B (Localization.AtPrime 𝔪') y := fun _ => rfl
  have hJ : J.map (Loc.map hN') = J.map (algebraMap D.B (Localization.AtPrime 𝔪')) := rfl
  rw [← D.map_algebraMap_B hg', halg, hJ,
    IsLocalization.mem_map_algebraMap_iff (𝔪'.primeCompl.map (algebraMap A D.B))] at hx
  obtain ⟨⟨j, ⟨_, s, hs, rfl⟩⟩, hj⟩ := hx
  simp only at hj
  have hinj : Function.Injective (Loc.map hN') :=
    Loc.map_injective hN' (Ideal.primeCompl_le_nonZeroDivisors 𝔪')
  rw [← halg, ← halg, ← map_mul] at hj
  refine ⟨s, hs, ?_⟩
  rw [map_mul, mul_comm, hinj hj]
  exact j.2

variable (hI : I ≠ ⊥)
include hI

omit [Algebra.Smooth ℚ A] in
/-- The two charts give the same ideals at common points. -/
lemma RFB_map_eq {𝔪₁ : Ideal A} [𝔪₁.IsMaximal] (D₁ : LocData I v₀ 𝔪₁) {𝔪' : Ideal A}
    [𝔪'.IsMaximal] (hg : D.g ∉ 𝔪') (hg₁ : D₁.g ∉ 𝔪') (t : ℚ) :
    (D.RFB t).map (Loc.map (D.ctrlN 𝔪' hg)) = (D₁.RFB t).map (Loc.map (D₁.ctrlN 𝔪' hg₁)) := by
  by_cases hZ : I ≤ 𝔪' ∧ InvAt I 𝔪' v₀
  · rw [D.RFB_map_of_mem hI hg hZ.1 hZ.2, D₁.RFB_map_of_mem hI hg₁ hZ.1 hZ.2]
  · rw [D.RFB_map_of_not_mem hg hZ, D₁.RFB_map_of_not_mem hg₁ hZ]

/-- **Spreading a membership** from one chart to another, up to a power of `g`. -/
lemma exists_pow_mul_mem {𝔪₁ : Ideal A} [𝔪₁.IsMaximal] (D₁ : LocData I v₀ 𝔪₁) (b : A) (t : ℚ)
    (hb : algebraMap A D.B b ∈ D.RFB t) :
    ∃ N : ℕ, algebraMap A D₁.B (D.g ^ N * b) ∈ D₁.RFB t := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℚ)
  have : IsJacobsonRing D₁.B := isJacobsonRing_localization (y := D₁.g)
  set 𝔠 := (D₁.RFB t).colon (Ideal.span {algebraMap A D₁.B b})
  have hrad : algebraMap A D₁.B D.g ∈ 𝔠.radical := by
    have hj : 𝔠.radical.jacobson = 𝔠.radical := IsJacobsonRing.out inferInstance (Ideal.radical_isRadical _)
    rw [← hj, Ideal.jacobson, Ideal.mem_sInf]
    rintro 𝔫 ⟨h𝔠𝔫, h𝔫⟩
    have hmax := (IsLocalization.isMaximal_iff_isMaximal_disjoint D₁.B D₁.g 𝔫).1 h𝔫
    set 𝔪' := 𝔫.under A
    have : 𝔪'.IsMaximal := hmax.1
    have hg₁ : D₁.g ∉ 𝔪' := hmax.2
    by_contra hg𝔫
    have hg : D.g ∉ 𝔪' := hg𝔫
    -- the image of `b` at `𝔪'` lies in the chart ideal of `D₁`
    have h1 : algebraMap A (Localization.AtPrime 𝔪') b ∈ (D₁.RFB t).map (Loc.map (D₁.ctrlN 𝔪' hg₁)) := by
      rw [← D.RFB_map_eq hI D₁ hg hg₁, ← D.map_algebraMap_B hg]
      exact Ideal.mem_map_of_mem _ hb
    obtain ⟨y, hy, hyb⟩ := D₁.exists_of_mem_map hg₁ _ h1
    apply hy
    show algebraMap A D₁.B y ∈ 𝔫
    apply h𝔠𝔫
    apply Ideal.le_radical
    rw [Submodule.mem_colon]
    intro z hz
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    rw [smul_eq_mul, ← mul_assoc, mul_comm _ w, mul_assoc, ← map_mul]
    exact Ideal.mul_mem_left _ _ hyb
  obtain ⟨N, hN⟩ := hrad
  refine ⟨N, ?_⟩
  have := Submodule.mem_colon.1 hN (algebraMap A D₁.B b) (Ideal.mem_span_singleton_self _)
  rwa [smul_eq_mul, ← map_pow, ← map_mul] at this

end LocData

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

/-- The weighted ideals of the centre along the component `V(𝔭)` (defined pointwise). -/
def compF (I : Ideal A) (𝔭 : Ideal A) (t : ℚ) : Ideal A :=
  ⨅ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal) (_ : 𝔭 ≤ 𝔪),
    (cRF I 𝔪 t).comap (algebraMap A (Localization.AtPrime 𝔪))

omit [IsDomain A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
lemma mem_compF {I 𝔭 : Ideal A} {t : ℚ} {f : A} :
    f ∈ compF I 𝔭 t ↔ ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], 𝔭 ≤ 𝔪 →
      algebraMap A (Localization.AtPrime 𝔪) f ∈ cRF I 𝔪 t := by
  simp only [compF, Submodule.mem_iInf, Ideal.mem_comap]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes)
include hI hmax h𝔭

/-- **The component filtration localizes to the maximal centres.** -/
theorem compF_map (𝔪₀ : Ideal A) [𝔪₀.IsMaximal] (h𝔭𝔪 : 𝔭 ≤ 𝔪₀) (t : ℚ) :
    (compF I 𝔭 t).map (algebraMap A (Localization.AtPrime 𝔪₀)) = cRF I 𝔪₀ t := by
  classical
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    exact mem_compF.1 hf 𝔪₀ h𝔭𝔪
  intro z hz
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq 𝔪₀.primeCompl z
  have ha : algebraMap A (Localization.AtPrime 𝔪₀) a ∈ cRF I 𝔪₀ t := by
    have := (cRF I 𝔪₀ t).mul_mem_right (algebraMap A _ s) hz
    rwa [IsLocalization.mk'_spec] at this
  suffices h : algebraMap A (Localization.AtPrime 𝔪₀) a ∈
      (compF I 𝔭 t).map (algebraMap A (Localization.AtPrime 𝔪₀)) by
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ h
  -- local data at the points of `V(𝔭)`
  set S := {𝔪 : Ideal A // 𝔪.IsMaximal ∧ 𝔭 ≤ 𝔪}
  have hD : ∀ p : S, Nonempty (haveI := p.2.1; LocData I v₀ p.1) := fun p => by
    have := p.2.1
    have hZ := mem_maxLocus_of_minimal hI hmax h𝔭 p.1 p.2.2
    exact LocData.nonempty hI p.1 hZ.1 hZ.2
  let D : ∀ p : S, (haveI := p.2.1; LocData I v₀ p.1) := fun p => (hD p).some
  let gS : S → A := fun p => haveI := p.2.1; (D p).g
  have hgS : ∀ p : S, gS p ∉ p.1 := fun p => by have := p.2.1; exact (D p).hg
  -- the chart at `𝔪₀`
  have hZ₀ := mem_maxLocus_of_minimal hI hmax h𝔭 𝔪₀ h𝔭𝔪
  obtain ⟨D₀⟩ := LocData.nonempty hI 𝔪₀ hZ₀.1 hZ₀.2
  -- Step 1: a multiple of `a` lies in the chart ideal at `𝔪₀`
  have h1 : algebraMap A (Localization.AtPrime 𝔪₀) a ∈
      (D₀.RFB t).map (Loc.map (D₀.ctrlN 𝔪₀ D₀.hg)) := by
    rw [D₀.RFB_map_of_mem hI D₀.hg hZ₀.1 hZ₀.2]; exact ha
  obtain ⟨s₁, hs₁, hs₁a⟩ := D₀.exists_of_mem_map D₀.hg _ h1
  -- Step 2: a finite cover of `V(𝔭)`
  have htop : 𝔭 ⊔ Ideal.span (Set.range gS) = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    set p : S := ⟨𝔪, h𝔪, le_sup_left.trans hle⟩
    exact hgS p (hle (le_sup_right (a := 𝔭) (Ideal.subset_span ⟨p, rfl⟩)))
  have hone : (1 : A) ∈ 𝔭 ⊔ Ideal.span (Set.range gS) := by rw [htop]; trivial
  obtain ⟨i, hi, y, hy, hiy⟩ := Submodule.mem_sup.1 hone
  obtain ⟨f, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hy
  -- Step 3: spread to each chart of the cover
  have h3 : ∀ p : S, ∃ N : ℕ, haveI := p.2.1;
      algebraMap A (D p).B (D₀.g ^ N * (s₁ * a)) ∈ (D p).RFB t :=
    fun p => by
      have := p.2.1
      exact D₀.exists_pow_mul_mem hI (D p) (s₁ * a) t hs₁a
  choose N hN using h3
  set M := ∑ p ∈ f.support, N p
  -- Step 4: the global element
  have hmem : D₀.g ^ M * s₁ * a ∈ compF I 𝔭 t := by
    rw [mem_compF]
    intro 𝔪' _ h𝔭𝔪'
    obtain ⟨p, hp, hp𝔪'⟩ : ∃ p ∈ f.support, gS p ∉ 𝔪' := by
      by_contra h
      push Not at h
      have : (1 : A) ∈ 𝔪' := by
        rw [← hiy]
        refine Ideal.add_mem _ (h𝔭𝔪' hi) ?_
        rw [Finsupp.sum]
        exact Ideal.sum_mem _ fun p hp => Ideal.mul_mem_left _ _ (h p hp)
      exact (Ideal.IsMaximal.ne_top ‹_›) ((Ideal.eq_top_iff_one _).2 this)
    have := p.2.1
    have hZ' := mem_maxLocus_of_minimal hI hmax h𝔭 𝔪' h𝔭𝔪'
    have h4 := Ideal.mem_map_of_mem (Loc.map ((D p).ctrlN 𝔪' hp𝔪')) (hN p)
    rw [(D p).RFB_map_of_mem hI hp𝔪' hZ'.1 hZ'.2, (D p).map_algebraMap_B hp𝔪'] at h4
    have hle : N p ≤ M := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hp
    have : D₀.g ^ M * s₁ * a = D₀.g ^ (M - N p) * (D₀.g ^ N p * (s₁ * a)) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle, mul_assoc]
    rw [this, map_mul]
    exact Ideal.mul_mem_left _ _ h4
  have hunit : IsUnit (algebraMap A (Localization.AtPrime 𝔪₀) (D₀.g ^ M * s₁)) :=
    IsLocalization.map_units _ (⟨D₀.g ^ M * s₁, 𝔪₀.primeCompl.mul_mem
      (𝔪₀.primeCompl.pow_mem D₀.hg M) hs₁⟩ : 𝔪₀.primeCompl)
  have h5 := Ideal.mem_map_of_mem (algebraMap A (Localization.AtPrime 𝔪₀)) hmem
  rw [map_mul] at h5
  exact (Ideal.unit_mul_mem_iff_mem _ hunit).1 h5

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

lemma Chart.RF_le_span {R : Type*} [CommRing R] [Algebra ℚ R] {n : ℕ} (c : Chart R n)
    (e : Fin n → ℚ) {t : ℚ} (ht : 0 < t) : c.RF e t ≤ Ideal.span (c.x '' {i | e i ≠ 0}) := by
  classical
  rw [Chart.RF, Ideal.span_le]
  rintro _ ⟨α, h0, hα, rfl⟩
  have : ∃ i, α i ≠ 0 := by
    by_contra h; push Not at h
    have : α = 0 := Finsupp.ext h
    rw [this, lam_zero] at hα; linarith
  obtain ⟨i, hi⟩ := this
  have hei : e i ≠ 0 := fun h => hi (h0 i h)
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  refine Ideal.mul_mem_right _ _ ?_
  exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_image_of_mem c.x hei)) _
    (Nat.pos_of_ne_zero hi)

omit [Algebra.Smooth ℚ A] in
lemma compF_antitone {I 𝔭 : Ideal A} {s t : ℚ} (hst : s ≤ t) (hI : I ≠ ⊥)
    (hZ : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], 𝔭 ≤ 𝔪 → I ≤ 𝔪 ∧ ∃ v, InvAt I 𝔪 v) :
    compF I 𝔭 t ≤ compF I 𝔭 s := by
  intro f hf
  rw [mem_compF] at hf ⊢
  intro 𝔪 _ h𝔭𝔪
  obtain ⟨hI𝔪, v, n, e, ⟨⟨J, hJ, rfl⟩, hmin⟩, -⟩ := hZ 𝔪 h𝔭𝔪
  have hJi : IsInv (Iloc I 𝔪) n J.e := ⟨⟨J, hJ, rfl⟩, hmin⟩
  have := hf 𝔪 h𝔭𝔪
  rw [cRF_eq hI hI𝔪 hJ hJi] at this ⊢
  exact J.c.RF_antitone J.e hst this

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes)
  {d : ℕ} (hd : 0 < d) (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
include hI hmax h𝔭 hd hw

omit hI hmax h𝔭 in
omit [Algebra.Smooth ℚ A] [IsNoetherianRing A] [IsDomain A] in
lemma LocData.le_ek {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪) {i : Fin D.n}
    (hi : D.ek i ≠ 0) : 1 / (d : ℚ) ≤ D.ek i := by
  obtain ⟨w, hw'⟩ := hw i
  have hv : v₀ i = D.ek i := by
    have := congrFun D.hv (i : ℕ); rw [ext0_apply] at this; exact this.symm
  rw [hv] at hw'
  have hpos : 0 < D.ek i := lt_of_le_of_ne (D.inv.nonneg i) (Ne.symm hi)
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hw0 : (0 : ℚ) < w := by rw [hw']; positivity
  have hw1 : (1 : ℚ) ≤ w := by
    have : 0 < w := by exact_mod_cast hw0
    exact_mod_cast this
  rw [div_le_iff₀ hdq]
  linarith [hw']

omit hI hmax h𝔭 hd hw in
omit [IsNoetherianRing A] [IsDomain A] [Algebra.Smooth ℚ A] in
lemma LocData.le {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪) : I ≤ 𝔪 := by
  obtain ⟨⟨J, hJ, -⟩, -⟩ := D.inv
  exact le_of_Iloc_le (hJ.trans (J.centred.RF_le_maximalIdeal one_pos))

omit hmax h𝔭 hd hw [Algebra.Smooth ℚ A] in
lemma LocData.cRF_eq_transport {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪) (t : ℚ) :
    cRF I 𝔪 t = (Loc.transport (D.ctrl 𝔪 D.hg) D.ck).RF D.ek t := by
  obtain ⟨⟨J, hJ, hJe⟩, hmin⟩ := D.inv
  have hJi : IsInv (Iloc I 𝔪) D.n J.e := ⟨⟨J, hJ, rfl⟩, by rw [hJe]; exact hmin⟩
  rw [cRF_eq hI D.le hJ hJi, D.rf 𝔪 D.hg J hJ hJe]

omit hmax h𝔭 [Algebra.Smooth ℚ A] in
lemma LocData.P_le_cRF {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪) :
    D.P ≤ cRF I 𝔪 (1 / d) := by
  rw [D.cRF_eq_transport hI, LocData.P, Ideal.span_le]
  rintro _ ⟨i, hi, rfl⟩
  have hne : D.ek i ≠ 0 := (D.supp i).2 hi
  exact (Loc.transport _ D.ck).RF_antitone D.ek (D.le_ek hd hw hne)
    ((Loc.transport _ D.ck).x_mem_RF D.ek i hne)

omit hmax h𝔭 [Algebra.Smooth ℚ A] in
lemma LocData.P_pow_le {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪) (N : ℕ) :
    D.P ^ N ≤ cRF I 𝔪 (N / d) := by
  have hv : InvAt I 𝔪 v₀ := ⟨D.n, D.ek, D.inv, D.hv⟩
  induction N with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_div, cRF_of_nonpos hI D.le hv le_rfl]
    exact le_top
  | succ N ih =>
    rw [pow_succ]
    refine (Ideal.mul_mono ih (D.P_le_cRF hI hd hw)).trans ?_
    have := cRF_mul_le hI D.le hv ((N : ℚ) / d) (1 / d)
    rwa [← add_div, ← Nat.cast_succ] at this

/-- Powers of the component prime lie in the filtration. -/
theorem pow_le_compF (N : ℕ) : 𝔭 ^ N ≤ compF I 𝔭 (N / d) := by
  intro f hf
  rw [mem_compF]
  intro 𝔪 _ h𝔭𝔪
  have hZ := mem_maxLocus_of_minimal hI hmax h𝔭 𝔪 h𝔭𝔪
  obtain ⟨D⟩ := LocData.nonempty hI 𝔪 hZ.1 hZ.2
  have hp : 𝔭 = D.p := D.eq_p_of_minimal h𝔭 h𝔭𝔪
  have h1 : algebraMap A (Localization.AtPrime 𝔪) f ∈ (𝔭 ^ N).map (algebraMap A _) :=
    Ideal.mem_map_of_mem _ hf
  rw [Ideal.map_pow, hp, D.map_p] at h1
  exact D.P_pow_le hI hd hw N h1

/-- Away from `V(𝔭)`, the component filtration is trivial. -/
theorem compF_map_of_not_le (𝔪₀ : Ideal A) [𝔪₀.IsMaximal] (h𝔭𝔪 : ¬ 𝔭 ≤ 𝔪₀) (t : ℚ) :
    (compF I 𝔭 t).map (algebraMap A (Localization.AtPrime 𝔪₀)) = ⊤ := by
  obtain ⟨π, hπ, hπ𝔪⟩ := Set.not_subset.1 h𝔭𝔪
  obtain ⟨N, hN⟩ := exists_nat_ge (t * d)
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hmem : π ^ N ∈ compF I 𝔭 t := by
    refine compF_antitone ?_ hI (fun 𝔪 _ h𝔭𝔪' => ?_) (pow_le_compF hI hmax h𝔭 hd hw N
      (Ideal.pow_mem_pow hπ N))
    · rw [le_div_iff₀ hdq]; exact hN
    · have hZ := mem_maxLocus_of_minimal hI hmax h𝔭 𝔪 h𝔭𝔪'
      exact ⟨hZ.1, v₀, hZ.2⟩
  have hu : IsUnit (algebraMap A (Localization.AtPrime 𝔪₀) (π ^ N)) :=
    IsLocalization.map_units _ (⟨π ^ N, 𝔪₀.primeCompl.pow_mem hπ𝔪 N⟩ : 𝔪₀.primeCompl)
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hmem) hu

/-- The first step of the component filtration is the component prime. -/
theorem compF_one_div : compF I 𝔭 (1 / d) = 𝔭 := by
  apply le_antisymm
  · intro f hf
    have := h𝔭.1.1
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal 𝔭 (Ideal.IsPrime.ne_top ‹_›)
    have := h𝔪
    have hZ := mem_maxLocus_of_minimal hI hmax h𝔭 𝔪 hle
    obtain ⟨D⟩ := LocData.nonempty hI 𝔪 hZ.1 hZ.2
    have hp : 𝔭 = D.p := D.eq_p_of_minimal h𝔭 hle
    have h1 := mem_compF.1 hf 𝔪 hle
    rw [D.cRF_eq_transport hI] at h1
    have h2 := Chart.RF_le_span _ D.ek (by positivity) h1
    have hset : {i | D.ek i ≠ 0} = {i : Fin D.n | (i : ℕ) < D.k} := by
      ext i; exact D.supp i
    rw [hset, ← LocData.P, ← D.map_p, ← hp] at h2
    rw [← under_map_atPrime hle]
    exact h2
  · have := pow_le_compF hI hmax h𝔭 hd hw 1
    rwa [pow_one, Nat.cast_one] at this

end BezoutCounterexample.Principalization

