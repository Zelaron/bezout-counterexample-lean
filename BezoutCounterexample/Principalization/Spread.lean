import BezoutCounterexample.Principalization.Local

/-!
# Localizations and spreading of Method-1 runs

Charts on localizations `M⁻¹A` of a `ℚ`-domain (`Loc.transport`), controlled enlargements of
submonoids (`Loc.Ext`, `Ctrl`), and `spread_run`: a Method-1 run at `A_𝔪` spreads to a run over
a localization `M'⁻¹A` controlled by a single element `g ∉ 𝔪`. Used for Theorem 3.3 (3) of the
paper.
-/

noncomputable section


namespace BezoutCounterexample.Principalization

open IsLocalization

/-- Charts are determined by their functions. -/
lemma Chart.eq_of_x {R : Type*} [CommRing R] [Algebra ℚ R] {n : ℕ} {c c' : Chart R n}
    (h : c.x = c'.x) : c = c' :=
  Chart.ext' h (funext fun i => c'.derivation_ext fun j => by rw [c'.d_x, ← h, c.d_x])

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A]

namespace Loc

/-- The algebra structure `M⁻¹A → N⁻¹A` for `M ≤ N`. -/
abbrev alg {M N : Submonoid A} (h : M ≤ N) : Algebra (Localization M) (Localization N) :=
  localizationAlgebraOfSubmonoidLe (Localization M) (Localization N) M N h

omit [IsDomain A] [Algebra ℚ A] in
lemma tower {M N : Submonoid A} (h : M ≤ N) :
    letI := alg h; IsScalarTower A (Localization M) (Localization N) :=
  localization_isScalarTower_of_submonoid_le _ _ M N h

omit [IsDomain A] [Algebra ℚ A] in
lemma isLoc {M N : Submonoid A} (h : M ≤ N) :
    letI := alg h; IsLocalization (N.map (algebraMap A (Localization M))) (Localization N) := by
  let := alg h
  have := tower h
  exact isLocalization_of_submonoid_le _ _ M N h

/-- The transition map `M⁻¹A → N⁻¹A`. -/
def map {M N : Submonoid A} (h : M ≤ N) : Localization M →+* Localization N :=
  letI := alg h; algebraMap (Localization M) (Localization N)

omit [IsDomain A] [Algebra ℚ A] in
lemma map_algebraMap {M N : Submonoid A} (h : M ≤ N) (a : A) :
    map h (algebraMap A (Localization M) a) = algebraMap A (Localization N) a := by
  let := alg h
  have := tower h
  exact (IsScalarTower.algebraMap_apply A (Localization M) (Localization N) a).symm

omit [IsDomain A] [Algebra ℚ A] in
lemma map_comp {M N P : Submonoid A} (h₁ : M ≤ N) (h₂ : N ≤ P) :
    (map h₂).comp (map h₁) = map (h₁.trans h₂) := by
  refine IsLocalization.ringHom_ext M (RingHom.ext fun a => ?_)
  simp only [RingHom.comp_apply, map_algebraMap]

omit [IsDomain A] [Algebra ℚ A] in
lemma map_apply_comp {M N P : Submonoid A} (h₁ : M ≤ N) (h₂ : N ≤ P) (x : Localization M) :
    map h₂ (map h₁ x) = map (h₁.trans h₂) x := by
  rw [← map_comp h₁ h₂]; rfl

variable {n : ℕ}

/-- Transport of a chart along `M⁻¹A → N⁻¹A`. -/
def transport {M N : Submonoid A} (h : M ≤ N) (c : Chart (Localization M) n) :
    Chart (Localization N) n :=
  letI := alg h
  haveI := isLoc h
  c.localization (N.map (algebraMap A (Localization M)))

omit [IsDomain A] in
@[simp] lemma transport_x {M N : Submonoid A} (h : M ≤ N) (c : Chart (Localization M) n) (i : Fin n) :
    (transport h c).x i = map h (c.x i) := rfl

omit [IsDomain A] in
lemma transport_d {M N : Submonoid A} (h : M ≤ N) (c : Chart (Localization M) n) (i : Fin n)
    (f : Localization M) : (transport h c).d i (map h f) = map h (c.d i f) := by
  let := alg h
  have := isLoc h
  exact Chart.localization_d _ c i f

omit [IsDomain A] in
lemma transport_trans {M N P : Submonoid A} (h₁ : M ≤ N) (h₂ : N ≤ P)
    (c : Chart (Localization M) n) :
    transport h₂ (transport h₁ c) = transport (h₁.trans h₂) c :=
  Chart.eq_of_x (funext fun i => by simp [map_apply_comp])

end Loc

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A]

namespace Loc

omit [IsDomain A] [Algebra ℚ A] in
lemma le_sup_powers {M N : Submonoid A} (h : M ≤ N) {s : A} (hs : s ∈ N) :
    M ⊔ Submonoid.powers s ≤ N :=
  sup_le h ((Submonoid.powers_le).2 hs)

omit [IsDomain A] [Algebra ℚ A] in
lemma mem_sup_powers (M : Submonoid A) (s : A) : s ∈ M ⊔ Submonoid.powers s :=
  Submonoid.mem_sup_right (Submonoid.mem_powers s)

omit [IsDomain A] [Algebra ℚ A] in
lemma map_mk' {M N : Submonoid A} (h : M ≤ N) (r : A) (t : M) :
    map h (mk' (Localization M) r t) = mk' (Localization N) r ⟨t, h t.2⟩ := by
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  simp only
  rw [← map_algebraMap h, ← map_algebraMap h, ← map_mul, IsLocalization.mk'_spec]

omit [IsDomain A] [Algebra ℚ A] in
lemma map_injective {M N : Submonoid A} (h : M ≤ N) (hN : N ≤ nonZeroDivisors A) :
    Function.Injective (map h) := by
  intro x y hxy
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M x
  obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective M y
  rw [map_mk', map_mk', IsLocalization.mk'_eq_iff_eq] at hxy
  rw [IsLocalization.mk'_eq_iff_eq]
  have hinj : Function.Injective (algebraMap A (Localization N)) :=
    IsLocalization.injective _ hN
  congr 1
  exact hinj hxy

omit [IsDomain A] [Algebra ℚ A] in
/-- Spreading an element. -/
lemma spread_elt {M N : Submonoid A} (h : M ≤ N) (a : Localization N) :
    ∃ (s : A) (hs : s ∈ N) (a' : Localization (M ⊔ Submonoid.powers s)),
      map (le_sup_powers h hs) a' = a := by
  obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective N a
  refine ⟨t, t.2, mk' _ r ⟨t, mem_sup_powers M t⟩, ?_⟩
  rw [map_mk']

end Loc

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] {n : ℕ}

lemma pushIdx_refl (β : Fin n →₀ ℕ) : pushIdx (le_refl n) β = β := by
  simp [pushIdx, Fin.castLE_refl]

lemma pad_refl (e : Fin n → ℚ) : pad n e = e := by
  funext i; simp [pad, i.2]

namespace Loc

variable {M N : Submonoid A}

omit [IsDomain A] in
lemma compat_transport (h : M ≤ N) (c : Chart (Localization M) n) :
    Compat (le_refl n) (map h) c (transport h c) :=
  ⟨fun i => by simp, fun i f => by simpa using transport_d h c i f,
    fun i hi => absurd i.2 (by omega)⟩

omit [IsDomain A] in
lemma transport_D (h : M ≤ N) (c : Chart (Localization M) n) (β : Fin n →₀ ℕ)
    (f : Localization M) : (transport h c).D β (map h f) = map h (c.D β f) := by
  have := (compat_transport h c).D β f
  rwa [pushIdx_refl] at this

omit [IsDomain A] in
lemma transport_Dv (h : M ≤ N) (c : Chart (Localization M) n) (β : Fin n →₀ ℕ)
    (f : Localization M) : (transport h c).Dv β (map h f) = map h (c.Dv β f) := by
  have := (compat_transport h c).Dv β f
  rwa [pushIdx_refl] at this

omit [IsDomain A] in
lemma map_RF (h : M ≤ N) (c : Chart (Localization M) n) (e : Fin n → ℚ) (t : ℚ) :
    (c.RF e t).map (map h) = (transport h c).RF e t := by
  rw [Chart.RF, Chart.RF, Ideal.map_span]
  congr 1
  ext f; constructor
  · rintro ⟨_, ⟨α, h0, ht, rfl⟩, rfl⟩
    exact ⟨α, h0, ht, by simp [map_prod, map_pow]⟩
  · rintro ⟨α, h0, ht, rfl⟩
    exact ⟨_, ⟨α, h0, ht, rfl⟩, by simp [map_prod, map_pow]⟩

omit [IsDomain A] in
lemma transport_nextChart (h : M ≤ N) (c : Chart (Localization M) n) (jj l : Fin n)
    (g : Localization M) (u : (Localization M)ˣ) (hu : c.d l g = u) :
    transport h (nextChart c jj l g u hu) =
      nextChart (transport h c) jj l (map h g) (Units.map (map h).toMonoidHom u)
        (by rw [transport_d, hu]; rfl) :=
  Chart.eq_of_x (funext fun i => by
    simp only [transport_x, Principalization.nextChart, Chart.reindex_x]
    by_cases hi : Equiv.swap jj l i = l
    · rw [hi, Chart.replace_x_self, Chart.replace_x_self]
    · rw [Chart.replace_x_ne _ _ _ _ _ hi, Chart.replace_x_ne _ _ _ _ _ hi, transport_x])

end Loc

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A]

namespace Loc

/-- `M` is controlled by `g`: at every prime not containing `g`, `M` consists of units. -/
def Ctrl (M : Submonoid A) (g : A) : Prop := ∀ (P : Ideal A) [P.IsPrime], g ∉ P → M ≤ P.primeCompl

omit [IsDomain A] [Algebra ℚ A] in
lemma Ctrl.sup_powers {M : Submonoid A} {g : A} (h : Ctrl M g) (s : A) :
    Ctrl (M ⊔ Submonoid.powers s) (g * s) := by
  intro P _ hgs
  have hg : g ∉ P := fun hg => hgs (P.mul_mem_right _ hg)
  have hs : s ∉ P := fun hs => hgs (P.mul_mem_left _ hs)
  exact sup_le (h P hg) ((Submonoid.powers_le).2 hs)

omit [IsDomain A] [Algebra ℚ A] in
lemma ctrl_powers (g : A) : Ctrl (Submonoid.powers g) g :=
  fun _P _ hg => (Submonoid.powers_le).2 hg

omit [IsDomain A] [Algebra ℚ A] in
lemma map_mem_map_trans {M₁ M₂ M₃ : Submonoid A} (h₁ : M₁ ≤ M₂) (h₂ : M₂ ≤ M₃)
    (J : Ideal (Localization M₁)) {x : Localization M₂} (hx : x ∈ J.map (map h₁)) :
    map h₂ x ∈ J.map (map (h₁.trans h₂)) := by
  rw [← map_comp h₁ h₂, ← Ideal.map_map]
  exact Ideal.mem_map_of_mem _ hx

variable {M N : Submonoid A}

omit [IsDomain A] [Algebra ℚ A] in
/-- Spreading membership in an extended ideal. -/
lemma spread_mem_map (h : M ≤ N) (hN : N ≤ nonZeroDivisors A) (J : Ideal (Localization M))
    (x : Localization M) (hx : map h x ∈ J.map (map h)) :
    ∃ (s : A) (_hs : s ∈ N), map (le_sup_left : M ≤ M ⊔ Submonoid.powers s) x ∈
      J.map (map (le_sup_left : M ≤ M ⊔ Submonoid.powers s)) := by
  let := alg h
  have := tower h
  have := isLoc h
  have hx' : algebraMap (Localization M) (Localization N) x ∈
      J.map (algebraMap (Localization M) (Localization N)) := hx
  rw [IsLocalization.mem_map_algebraMap_iff (N.map (algebraMap A (Localization M)))] at hx'
  obtain ⟨⟨⟨y, hy⟩, ⟨_, t, ht, rfl⟩⟩, heq⟩ := hx'
  simp only at heq
  refine ⟨t, ht, ?_⟩
  have hinj := map_injective h hN
  have key : x * algebraMap A (Localization M) t = y := by
    apply hinj
    rw [map_mul]
    exact heq
  set M' := M ⊔ Submonoid.powers t
  have hunit : IsUnit (algebraMap A (Localization M') t) :=
    IsLocalization.map_units (Localization M') ⟨t, mem_sup_powers M t⟩
  have : map (le_sup_left : M ≤ M') x * algebraMap A (Localization M') t ∈
      J.map (map (le_sup_left : M ≤ M')) := by
    rw [← map_algebraMap (le_sup_left : M ≤ M'), ← map_mul, key]
    exact Ideal.mem_map_of_mem _ hy
  obtain ⟨v, hv⟩ := hunit
  have := Ideal.mul_mem_right (↑v⁻¹ : Localization M') _ this
  rwa [← hv, mul_assoc, Units.mul_inv, mul_one] at this

end Loc

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A]

namespace Loc

/-- `M'` is a controlled enlargement of `M` inside `N`. -/
structure Ext (M N M' : Submonoid A) : Prop where
  le₁ : M ≤ M'
  le₂ : M' ≤ N
  ctrl : ∃ t ∈ N, ∀ g, Ctrl M g → Ctrl M' (g * t)

omit [IsDomain A] [Algebra ℚ A] in
lemma Ext.refl {M N : Submonoid A} (h : M ≤ N) : Ext M N M :=
  ⟨le_rfl, h, 1, N.one_mem, fun g hg => by rwa [mul_one]⟩

omit [IsDomain A] [Algebra ℚ A] in
lemma Ext.sup_powers {M N : Submonoid A} (h : M ≤ N) {s : A} (hs : s ∈ N) :
    Ext M N (M ⊔ Submonoid.powers s) :=
  ⟨le_sup_left, le_sup_powers h hs, s, hs, fun _g hg => hg.sup_powers s⟩

omit [IsDomain A] [Algebra ℚ A] in
lemma Ext.trans {M N M₁ M₂ : Submonoid A} (h₁ : Ext M N M₁) (h₂ : Ext M₁ N M₂) : Ext M N M₂ := by
  obtain ⟨t₁, ht₁, hc₁⟩ := h₁.ctrl
  obtain ⟨t₂, ht₂, hc₂⟩ := h₂.ctrl
  refine ⟨h₁.le₁.trans h₂.le₁, h₂.le₂, t₁ * t₂, N.mul_mem ht₁ ht₂, fun g hg => ?_⟩
  rw [← mul_assoc]; exact hc₂ _ (hc₁ g hg)

variable {M N : Submonoid A}

omit [IsDomain A] [Algebra ℚ A] in
/-- Spreading containment of an extended ideal. -/
lemma spread_ideal_le [IsNoetherianRing A] (h : M ≤ N) (hN : N ≤ nonZeroDivisors A)
    (I : Ideal A) (J : Ideal (Localization M))
    (hIJ : I.map (algebraMap A (Localization N)) ≤ J.map (map h)) :
    ∃ M', ∃ hE : Ext M N M', I.map (algebraMap A (Localization M')) ≤ J.map (map hE.le₁) := by
  classical
  obtain ⟨s, rfl⟩ := (IsNoetherian.noetherian I : I.FG)
  have key : ∀ t : Finset A, (t : Set A) ⊆ s → ∃ M', ∃ hE : Ext M N M', ∀ a ∈ t,
      algebraMap A (Localization M') a ∈ J.map (map hE.le₁) := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact fun _ => ⟨M, Ext.refl h, fun a ha => absurd ha (Finset.notMem_empty a)⟩
    | insert a t hat ih =>
      intro hts
      obtain ⟨M₁, hE₁, hmem₁⟩ := ih (fun x hx => hts (Finset.mem_insert_of_mem hx))
      have ha : map hE₁.le₂ (algebraMap A (Localization M₁) a) ∈
          (J.map (map hE₁.le₁)).map (map hE₁.le₂) := by
        rw [Ideal.map_map, map_comp, map_algebraMap]
        exact hIJ (Ideal.mem_map_of_mem _ (Ideal.subset_span (hts (Finset.mem_insert_self a t))))
      obtain ⟨u, hu, hmem⟩ := spread_mem_map hE₁.le₂ hN _ _ ha
      have hE₂ := Ext.sup_powers hE₁.le₂ hu
      refine ⟨_, hE₁.trans hE₂, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · rw [Ideal.map_map, map_comp, map_algebraMap] at hmem
        exact hmem
      · have := map_mem_map_trans hE₁.le₁ hE₂.le₁ J (hmem₁ x hx)
        rwa [map_algebraMap] at this
  obtain ⟨M', hE, hmem⟩ := key s (subset_refl _)
  refine ⟨M', hE, ?_⟩
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨a, ha, rfl⟩
  exact hmem a ha

omit [IsDomain A] [Algebra ℚ A] in
/-- Spreading an element of an extended ideal. -/
lemma spread_mem_ideal (h : M ≤ N) (I : Ideal A) {f : Localization N}
    (hf : f ∈ I.map (algebraMap A (Localization N))) :
    ∃ M', ∃ hE : Ext M N M', ∃ f' ∈ I.map (algebraMap A (Localization M')), map hE.le₂ f' = f := by
  rw [IsLocalization.mem_map_algebraMap_iff N] at hf
  obtain ⟨⟨⟨a, ha⟩, t⟩, heq⟩ := hf
  have hE := Ext.sup_powers h t.2
  refine ⟨_, hE, mk' _ a ⟨t, mem_sup_powers M t⟩, ?_, ?_⟩
  · rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
  · rw [map_mk', IsLocalization.mk'_eq_iff_eq_mul]
    exact heq.symm

omit [IsDomain A] [Algebra ℚ A] in
/-- Spreading a unit. -/
lemma spread_unit (h : M ≤ N) (hN : N ≤ nonZeroDivisors A) (u : (Localization N)ˣ) :
    ∃ M', ∃ hE : Ext M N M', ∃ u' : (Localization M')ˣ, map hE.le₂ u' = u := by
  obtain ⟨s₁, hs₁, a, ha⟩ := spread_elt h (u : Localization N)
  have hE₁ := Ext.sup_powers h hs₁
  obtain ⟨s₂, hs₂, b, hb⟩ := spread_elt hE₁.le₂ (↑u⁻¹ : Localization N)
  have hE₂ := Ext.sup_powers hE₁.le₂ hs₂
  set a' := map hE₂.le₁ a
  have hab : a' * b = 1 := by
    apply map_injective hE₂.le₂ hN
    rw [map_mul, map_one, hb, map_apply_comp, ha, Units.mul_inv]
  refine ⟨_, hE₁.trans hE₂, ⟨a', b, hab, by rw [mul_comm, hab]⟩, ?_⟩
  change map hE₂.le₂ (map hE₂.le₁ a) = u
  rw [map_apply_comp, ha]

omit [IsDomain A] [Algebra ℚ A] in
/-- Spreading the unit property. -/
lemma spread_isUnit (h : M ≤ N) (hN : N ≤ nonZeroDivisors A) {x : Localization M}
    (hx : IsUnit (map h x)) :
    ∃ M', ∃ hE : Ext M N M', IsUnit (map hE.le₁ x) := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨s, hs, b, hb⟩ := spread_elt h (↑u⁻¹ : Localization N)
  have hE := Ext.sup_powers h hs
  have hxb : map hE.le₁ x * b = 1 := by
    apply map_injective hE.le₂ hN
    rw [map_mul, map_one, hb, map_apply_comp, ← hu, Units.mul_inv]
  exact ⟨_, hE, IsUnit.of_mul_eq_one _ hxb⟩

end Loc

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalization IsLocalRing

lemma MC.ext' {R : Type*} [CommRing R] [Algebra ℚ R] [IsLocalRing R] {n : ℕ} {J J' : MC R n}
    (hc : J.c = J'.c) (he : J.e = J'.e) : J = J' := by
  cases J; cases J'; simp only at hc he; subst hc; subst he; rfl

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [IsNoetherianRing A]
  (𝔪 : Ideal A) [𝔪.IsMaximal] {n : ℕ} (I : Ideal A)

omit [IsNoetherianRing A] [IsDomain A] [Algebra ℚ A] in
lemma Loc.map_map_algebraMap {M N : Submonoid A} (h : M ≤ N) (J : Ideal A) :
    (J.map (algebraMap A (Localization M))).map (Loc.map h) =
      J.map (algebraMap A (Localization N)) := by
  rw [Ideal.map_map]
  congr 1
  exact RingHom.ext fun a => Loc.map_algebraMap h a

lemma spread_adm {M : Submonoid A} (hM : M ≤ 𝔪.primeCompl) (c : Chart (Localization M) n)
    (e : Fin n → ℚ)
    (hadm : I.map (algebraMap A (Localization.AtPrime 𝔪)) ≤ (Loc.transport hM c).RF e 1) :
    ∃ M', ∃ hE : Loc.Ext M 𝔪.primeCompl M',
      I.map (algebraMap A (Localization M')) ≤ (Loc.transport hE.le₁ c).RF e 1 := by
  rw [← Loc.map_RF] at hadm
  obtain ⟨M', hE, hle⟩ := Loc.spread_ideal_le hM (Ideal.primeCompl_le_nonZeroDivisors 𝔪) I _ hadm
  exact ⟨M', hE, by rwa [← Loc.map_RF]⟩

/-- **Spreading of Method-1 runs**: a run at the local ring `A_𝔪` comes from a run over a
localization `M'⁻¹A` with `M'` controlled by a single element outside `𝔪`. -/
theorem spread_run :
    ∀ (d j : ℕ), n - j = d → ∀ (M : Submonoid A) (hM : M ≤ 𝔪.primeCompl)
      (c : Chart (Localization M) n) (e : Fin n → ℚ) (hc : (Loc.transport hM c).IsCentred)
      (hnn : ∀ i, 0 ≤ e i) (ha : Antitone e),
      MC.SA (I.map (algebraMap A (Localization.AtPrime 𝔪))) j
        ⟨Loc.transport hM c, e, hc, hnn, ha⟩ →
      ∃ M', ∃ hE : Loc.Ext M 𝔪.primeCompl M', ∃ (k : ℕ) (ck : Chart (Localization M') n)
        (ek : Fin n → ℚ),
        IsRun (I.map (algebraMap A (Localization M'))) j (Loc.transport hE.le₁ c) e k ck ek ∧
        I.map (algebraMap A (Localization M')) ≤ ck.RF ek 1 ∧
        (∀ i, ek i ≠ 0 ↔ (i : ℕ) < k) ∧ (∀ i, 0 ≤ ek i) ∧ Antitone ek ∧
        (Loc.transport hE.le₂ ck).IsCentred := by
  have hN : 𝔪.primeCompl ≤ nonZeroDivisors A := Ideal.primeCompl_le_nonZeroDivisors 𝔪
  intro d
  induction d with
  | zero =>
    intro j hj M hM c e hc hnn ha hSA
    by_cases hadm : MC.Adm (I.map (algebraMap A (Localization.AtPrime 𝔪)))
        (⟨Loc.transport hM c, e, hc, hnn, ha⟩ : MC (Localization.AtPrime 𝔪) n)
    · obtain ⟨M', hE, hle⟩ := spread_adm 𝔪 I hM c e hadm
      exact ⟨M', hE, j, _, e, .refl _ _ _, hle, hSA.supp, hnn, ha,
        by rw [Loc.transport_trans]; exact hc⟩
    · obtain ⟨hjn, -⟩ := hSA.step_data hadm
      omega
  | succ d ih =>
    intro j hj M hM c e hc hnn ha hSA
    set Jc := Loc.transport hM c with hJc
    by_cases hadm : MC.Adm (I.map (algebraMap A (Localization.AtPrime 𝔪)))
        (⟨Jc, e, hc, hnn, ha⟩ : MC (Localization.AtPrime 𝔪) n)
    · obtain ⟨M', hE, hle⟩ := spread_adm 𝔪 I hM c e hadm
      exact ⟨M', hE, j, _, e, .refl _ _ _, hle, hSA.supp, hnn, ha,
        by rw [Loc.transport_trans]; exact hc⟩
    obtain ⟨hjn, f, hf, β, l, hl, hβl, hlam, hNt, hunit, hb, u, hu, hc', hnn', ha', hSA'⟩ :=
      hSA.step_run hadm
    -- spread `f`
    obtain ⟨M₁, hE₁, f₁, hf₁, hf₁m⟩ := Loc.spread_mem_ideal hM I hf
    set c₁ := Loc.transport hE₁.le₁ c
    have hJc₁ : Jc = Loc.transport hE₁.le₂ c₁ := by rw [Loc.transport_trans]
    -- spread the witness unit
    have hw : IsUnit (Loc.map hE₁.le₂ (c₁.D β f₁)) := by
      rw [← Loc.transport_D, ← hJc₁, hf₁m]; exact hunit
    obtain ⟨M₂, hE₂, hw₂⟩ := Loc.spread_isUnit hE₁.le₂ hN hw
    -- spread `u`
    obtain ⟨M₃, hE₃, u₃, hu₃m⟩ := Loc.spread_unit hE₂.le₂ hN u
    have h13 : M₁ ≤ M₃ := hE₂.le₁.trans hE₃.le₁
    set c₃ := Loc.transport h13 c₁ with hc₃
    set f₃ := Loc.map h13 f₁ with hf₃
    have hJc₃ : Jc = Loc.transport hE₃.le₂ c₃ := by rw [hc₃, Loc.transport_trans, hJc₁]
    have hf₃m : Loc.map hE₃.le₂ f₃ = f := by rw [hf₃, Loc.map_apply_comp, hf₁m]
    set γ := β - Finsupp.single l 1
    have hmapx : Loc.map hE₃.le₂ (c₃.Dv γ f₃) = Jc.Dv γ f := by
      rw [← Loc.transport_Dv, ← hJc₃, hf₃m]
    have hu₃ : c₃.d l (c₃.Dv γ f₃) = u₃ := by
      apply Loc.map_injective hE₃.le₂ hN
      rw [← Loc.transport_d, ← hJc₃, hmapx, hu, hu₃m]
    have hw₃ : IsUnit (c₃.D β f₃) := by
      have : c₃.D β f₃ = Loc.map hE₃.le₁ (Loc.map hE₂.le₁ (c₁.D β f₁)) := by
        rw [hc₃, hf₃, Loc.transport_D, Loc.map_apply_comp]
      rw [this]; exact hw₂.map _
    set C₃ := nextChart c₃ ⟨j, hjn⟩ l (c₃.Dv γ f₃) u₃ hu₃ with hC₃
    have hC₃N : Loc.transport hE₃.le₂ C₃ = nextChart Jc ⟨j, hjn⟩ l (Jc.Dv γ f) u hu := by
      rw [hC₃, Loc.transport_nextChart]
      refine Chart.eq_of_x (funext fun i => ?_)
      simp only [Principalization.nextChart, Chart.reindex_x]
      by_cases hi : Equiv.swap ⟨j, hjn⟩ l i = l
      · rw [hi, Chart.replace_x_self, Chart.replace_x_self, hmapx]
      · rw [Chart.replace_x_ne _ _ _ _ _ hi, Chart.replace_x_ne _ _ _ _ _ hi, hJc₃]
    have hcC : (Loc.transport hE₃.le₂ C₃).IsCentred := by rw [hC₃N]; exact hc'
    have hSA'' : MC.SA (I.map (algebraMap A (Localization.AtPrime 𝔪))) (j + 1)
        ⟨Loc.transport hE₃.le₂ C₃, nextE e j (nextW e j β), hcC, hnn', ha'⟩ := by
      have heq : (⟨Loc.transport hE₃.le₂ C₃, nextE e j (nextW e j β), hcC, hnn', ha'⟩ :
          MC (Localization.AtPrime 𝔪) n) = ⟨nextChart Jc ⟨j, hjn⟩ l (Jc.Dv γ f) u hu,
            nextE e j (nextW e j β), hc', hnn', ha'⟩ := MC.ext' hC₃N rfl
      rw [heq]; exact hSA'
    obtain ⟨M', hE', k, ck, ek, hrun, hadm', hsupp', hnn'', ha'', hcent⟩ :=
      ih (j + 1) (by omega) M₃ hE₃.le₂ C₃ _ hcC hnn' ha' hSA''
    have hE : Loc.Ext M 𝔪.primeCompl M' := hE₁.trans (hE₂.trans (hE₃.trans hE'))
    refine ⟨M', hE, k, ck, ek, ?_, hadm', hsupp', hnn'', ha'', hcent⟩
    -- the step over `M'⁻¹A`
    set c' := Loc.transport hE.le₁ c with hc'def
    have hc'3 : c' = Loc.transport hE'.le₁ c₃ := by
      rw [hc'def, hc₃, Loc.transport_trans, Loc.transport_trans]
    obtain ⟨f', hf'def⟩ : ∃ f', f' = Loc.map hE'.le₁ f₃ := ⟨_, rfl⟩
    have hf' : f' ∈ I.map (algebraMap A (Localization M')) := by
      have := Ideal.mem_map_of_mem (Loc.map hE'.le₁) (Ideal.mem_map_of_mem (Loc.map h13) hf₁)
      rw [Loc.map_map_algebraMap, Loc.map_map_algebraMap] at this
      rw [hf'def]; exact this
    have hmapx' : Loc.map hE'.le₁ (c₃.Dv γ f₃) = c'.Dv γ f' := by
      rw [hc'3, hf'def, Loc.transport_Dv hE'.le₁]
    have hu' : c'.d l (c'.Dv γ f') = ↑(Units.map (Loc.map hE'.le₁).toMonoidHom u₃) := by
      rw [← hmapx', hc'3, Loc.transport_d hE'.le₁, hu₃]; rfl
    have hw' : IsUnit (c'.D β f') := by
      rw [hc'3, hf'def, Loc.transport_D hE'.le₁]; exact hw₃.map _
    have hnext : nextChart c' ⟨j, hjn⟩ l (c'.Dv γ f') (Units.map (Loc.map hE'.le₁).toMonoidHom u₃)
        hu' = Loc.transport hE'.le₁ C₃ := by
      rw [hC₃, Loc.transport_nextChart]
      refine Chart.eq_of_x (funext fun i => ?_)
      simp only [Principalization.nextChart, Chart.reindex_x]
      by_cases hi : Equiv.swap ⟨j, hjn⟩ l i = l
      · rw [hi, Chart.replace_x_self, Chart.replace_x_self, hmapx']
      · rw [Chart.replace_x_ne _ _ _ _ _ hi, Chart.replace_x_ne _ _ _ _ _ hi, hc'3]
    refine IsRun.step hjn f' hf' β l hl hβl hlam hNt hw' hb _ hu' ?_
    rw [hnext]
    exact hrun

end BezoutCounterexample.Principalization

