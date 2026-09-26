import BezoutCounterexample.Principalization.ReesVertex

/-!
# The drop of the invariant

Theorem 3.6 (`thm:drop`) of the paper.

* `InvAt.of_ringEquiv`: invariants are preserved by automorphisms preserving the ideal.
* `reesScale_weakT`: the weak transform is `𝔾_m`-stable.
* `drop` (Brais, property (C)): at every closed point of the exceptional divisor of the Rees
  algebra off `V(R₊)`, the weak transform has strictly smaller invariant than the maximal
  invariant of `I`.  Proof: the invariant at the vertex is the old one (`vertexG_data`), upper
  semicontinuity near the vertex (`local_inv` on the smooth Rees algebra), and the `𝔾_m`-action
  moving any such point into a neighbourhood of the vertex (`exists_reesScale_not_mem`).
-/

noncomputable section


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

section Aux

variable {T : Type} [CommRing T] [Algebra ℚ T]

/-- **Invariants are preserved by ring automorphisms** preserving the ideal. -/
lemma InvAt.of_ringEquiv (σ : T ≃+* T) {I : Ideal T} (hI : I.map σ = I) (Q : Ideal T)
    [Q.IsPrime] {v : ℕ → ℚ} (h : InvAt I (Q.comap σ) v) : InvAt I Q v := by
  have H : (Q.comap σ).primeCompl.map σ.toMonoidHom = Q.primeCompl := by
    ext x
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, Ideal.mem_comap]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨σ.symm x, by simpa using hx, by simp⟩
  let ψ : Localization.AtPrime (Q.comap σ) ≃+* Localization.AtPrime Q :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime (Q.comap σ))
      (Localization.AtPrime Q) σ H
  have hψ : ∀ x : T, ψ (algebraMap T _ x) = algebraMap T _ (σ x) :=
    fun x => IsLocalization.ringEquivOfRingEquiv_eq H x
  obtain ⟨n, e, he, hev⟩ := h
  refine ⟨n, e, ?_, hev⟩
  have h1 := he.mapRingEquiv ψ
  have h2 : (Iloc I (Q.comap σ)).map ψ = Iloc I Q := by
    show (I.map (algebraMap T (Localization.AtPrime (Q.comap σ)))).map
      (ψ : Localization.AtPrime (Q.comap σ) →+* Localization.AtPrime Q) = _
    rw [Ideal.map_map]
    have : (ψ : Localization.AtPrime (Q.comap σ) →+* Localization.AtPrime Q).comp
        (algebraMap T _) = (algebraMap T (Localization.AtPrime Q)).comp (σ : T →+* T) :=
      RingHom.ext fun x => hψ x
    rw [this, ← Ideal.map_map]
    congr 1
  rwa [h2] at h1

lemma ext0_lt {n : ℕ} {e e' : Fin n → ℚ} (h : toLex e < toLex e') :
    toLex (ext0 e) < toLex (ext0 e') := by
  obtain ⟨i, hbelow, hi⟩ := h
  refine ⟨i, fun j hj => ?_, ?_⟩
  · simp only [Pi.toLex_apply] at hbelow ⊢
    have hjn : j < n := lt_trans hj i.2
    have := hbelow ⟨j, hjn⟩ hj
    simp only [ext0, dif_pos hjn]; exact this
  · simp only [Pi.toLex_apply] at hi ⊢
    simp only [ext0, dif_pos i.2]; exact hi

end Aux

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

section WeakFacts

variable {B : Type*} [CommRing B] [Algebra ℚ B] [IsDomain B] (Φ : WFil B)

lemma weakT_ne_bot {I : Ideal B} (hI : I ≠ ⊥) (d : ℤ) (hId : I ≤ Φ.F d) : weakT Φ I d hId ≠ ⊥ := by
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  intro h
  have hmem : (⟨LaurentPolynomial.C f * T d, C_mul_T_mem_ReesAlg (hId hf)⟩ : ReesAlg Φ) ∈
      weakT Φ I d hId := Ideal.subset_span ⟨⟨f, hf⟩, rfl⟩
  rw [h, Ideal.mem_bot] at hmem
  have := congrArg (fun p : ReesAlg Φ => (p : B[T;T⁻¹]).coeff d) hmem
  simp only [coeff_C_mul_T, if_pos rfl] at this
  exact hf0 (by simpa using this)

lemma weakT_le {I : Ideal B} (d : ℤ) (hId : I ≤ Φ.F d) (P : Ideal (ReesAlg Φ))
    (h : ∀ f (hf : f ∈ I), (⟨LaurentPolynomial.C f * T d, C_mul_T_mem_ReesAlg (hId hf)⟩ :
      ReesAlg Φ) ∈ P) : weakT Φ I d hId ≤ P := by
  rw [weakT, Ideal.span_le]
  rintro _ ⟨⟨f, hf⟩, rfl⟩
  exact h f hf

lemma reesScale_weakT_le (μ : Bˣ) {I : Ideal B} (d : ℤ) (hId : I ≤ Φ.F d) :
    (weakT Φ I d hId).map (reesScale Φ μ) ≤ weakT Φ I d hId := by
  rw [Ideal.map_le_iff_le_comap]
  apply weakT_le
  intro f hf
  rw [Ideal.mem_comap]
  have : reesScale Φ μ ⟨LaurentPolynomial.C f * T d, C_mul_T_mem_ReesAlg (hId hf)⟩ =
      algebraMap B (ReesAlg Φ) ↑(μ ^ d) * ⟨LaurentPolynomial.C f * T d, C_mul_T_mem_ReesAlg (hId hf)⟩ := by
    apply Subtype.ext
    rw [reesScale_coe]
    show lscale μ (LaurentPolynomial.C f * T d) =
      algebraMap B B[T;T⁻¹] ↑(μ ^ d) * (LaurentPolynomial.C f * T d)
    rw [lscale_C_mul_T, ← LaurentPolynomial.C_eq_algebraMap, ← mul_assoc, ← map_mul, mul_comm f]
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨f, hf⟩, rfl⟩)

lemma reesScale_weakT (μ : Bˣ) {I : Ideal B} (d : ℤ) (hId : I ≤ Φ.F d) :
    (weakT Φ I d hId).map (reesScale Φ μ) = weakT Φ I d hId := by
  refine le_antisymm (reesScale_weakT_le Φ μ d hId) ?_
  intro x hx
  have h1 := reesScale_weakT_le Φ μ⁻¹ d hId (Ideal.mem_map_of_mem _ hx)
  have h2 := Ideal.mem_map_of_mem (reesScale Φ μ) h1
  have : reesScale Φ μ (reesScale Φ μ⁻¹ x) = x := by
    apply Subtype.ext
    rw [reesScale_coe, reesScale_coe, lscale_lscale, mul_inv_cancel, lscale_one]
  rwa [this] at h2

end WeakFacts

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

/-- Pulling back membership from a prime localization to a controlled localization. -/
lemma Loc.exists_of_mem_map {T : Type} [CommRing T] [IsDomain T] [Algebra ℚ T]
    {M : Submonoid T} {Q : Ideal T} [Q.IsPrime] (h : M ≤ Q.primeCompl)
    (J : Ideal (Localization M)) {x : T}
    (hx : algebraMap T (Localization.AtPrime Q) x ∈ J.map (Loc.map h)) :
    ∃ s : T, s ∉ Q ∧ algebraMap T (Localization M) (s * x) ∈ J := by
  letI := Loc.alg h
  haveI := Loc.tower h
  haveI := Loc.isLoc h
  have halg : ∀ y : Localization M, Loc.map h y = algebraMap (Localization M) (Localization Q.primeCompl) y :=
    fun _ => rfl
  have hJ : J.map (Loc.map h) = J.map (algebraMap (Localization M) (Localization Q.primeCompl)) := rfl
  rw [← Loc.map_algebraMap h, halg, hJ,
    IsLocalization.mem_map_algebraMap_iff (Q.primeCompl.map (algebraMap T (Localization M)))] at hx
  obtain ⟨⟨j, ⟨_, s, hs, rfl⟩⟩, hj⟩ := hx
  simp only at hj
  have hinj : Function.Injective (Loc.map h) :=
    Loc.map_injective h (Ideal.primeCompl_le_nonZeroDivisors Q)
  rw [← halg, ← halg, ← map_mul] at hj
  refine ⟨s, hs, ?_⟩
  rw [map_mul, mul_comm, hinj hj]
  exact j.2

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
include hI hmax h𝔭 hd hw

/-- **The drop of the invariant on the exceptional divisor** (Brais, property (C)): at every point
of the Rees algebra on the exceptional divisor and off the vertex locus `V(R₊)`, the weak transform
has strictly smaller invariant. -/
theorem drop (P : Ideal (ReesAlg (compFil hI hmax h𝔭 d))) [hPm : P.IsMaximal]
    (hIwP : weakT (compFil hI hmax h𝔭 d) I d (I_le_compFil hI hmax h𝔭 hd) ≤ P)
    (hsP : reesS (compFil hI hmax h𝔭 d) (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj) ∈ P)
    {j : ℤ} (hj : 1 ≤ j) {f : A} (hf : f ∈ (compFil hI hmax h𝔭 d).F j)
    (hyP : (⟨LaurentPolynomial.C f * T j, C_mul_T_mem_ReesAlg hf⟩ :
      ReesAlg (compFil hI hmax h𝔭 d)) ∉ P)
    {v : ℕ → ℚ} (hv : InvAt (weakT (compFil hI hmax h𝔭 d) I d (I_le_compFil hI hmax h𝔭 hd)) P v) :
    toLex v₀ < toLex v := by
  classical
  have hneg : ∀ j : ℤ, j ≤ 0 → (compFil hI hmax h𝔭 d).F j = ⊤ := fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj
  have hId := I_le_compFil hI hmax h𝔭 hd
  haveI : Algebra.FiniteType A (ReesAlg (compFil hI hmax h𝔭 d)) := reesAlg_finiteType hI hmax h𝔭 d hd hw
  haveI : Algebra.FiniteType ℚ (ReesAlg (compFil hI hmax h𝔭 d)) := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  haveI : IsNoetherianRing (ReesAlg (compFil hI hmax h𝔭 d)) := Algebra.FiniteType.isNoetherianRing A (ReesAlg (compFil hI hmax h𝔭 d))
  haveI : Algebra.Smooth ℚ (ReesAlg (compFil hI hmax h𝔭 d)) := rees_smooth hI hmax h𝔭 hd hw
  -- the point of `A` below `P`
  set 𝔪 := P.comap (algebraMap A (ReesAlg (compFil hI hmax h𝔭 d)))
  haveI : 𝔪.IsMaximal := comap_isMaximal_of_finiteType P
  have h𝔭𝔪 : 𝔭 ≤ 𝔪 := by
    intro g hg
    have hg1 : g ∈ (compFil hI hmax h𝔭 d).F 1 := by
      rw [compFil_F, show ((1 : ℤ) : ℚ) / d = 1 / d by push_cast; ring, compF_one_div hI hmax h𝔭 hd hw]
      exact hg
    show algebraMap A (ReesAlg (compFil hI hmax h𝔭 d)) g ∈ P
    have : algebraMap A (ReesAlg (compFil hI hmax h𝔭 d)) g = reesS (compFil hI hmax h𝔭 d) hneg * ⟨LaurentPolynomial.C g * T 1, C_mul_T_mem_ReesAlg hg1⟩ := by
      apply Subtype.ext
      show algebraMap A A[T;T⁻¹] g = T (-1) * (LaurentPolynomial.C g * T 1)
      rw [mul_left_comm, ← T_add, neg_add_cancel, T_zero, mul_one, LaurentPolynomial.C_eq_algebraMap]
    rw [this]; exact P.mul_mem_right _ hsP
  obtain ⟨D⟩ := VertexData.nonempty hI hmax h𝔭 hd hw 𝔪 h𝔭𝔪
  set hpos := D.hpos hd
  set P₀ := vertexG (compFil hI hmax h𝔭 d) 𝔪 hpos
  obtain ⟨J₀, hJ₀adm, hJ₀e, hJ₀inv, hJ₀homog⟩ := D.vertexG_data hd
  -- the weak transform near the vertex
  have hIw0 : (weakT (compFil hI hmax h𝔭 d) I d hId) ≠ ⊥ := weakT_ne_bot (compFil hI hmax h𝔭 d) hI d hId
  have hIwP₀ : (weakT (compFil hI hmax h𝔭 d) I d hId) ≤ P₀ := by
    apply weakT_le
    intro g hg
    rw [mem_vertexG, coeff_C_mul_T, if_neg (by omega)]
    exact zero_mem _
  obtain ⟨n', M', g, hg, hctrl, k', ck, ek, hsupp', hadm', hinv', hcent', hbound'⟩ :=
    local_inv (weakT (compFil hI hmax h𝔭 d) I d hId) hIw0 P₀ hIwP₀
  obtain rfl := hinv'.card_eq J₀.c
  have hek : ek = pad (D.n + 1) D.J.e := by
    rw [← hJ₀e]; exact hinv'.unique hJ₀inv
  -- homogeneous elements lie in the chart ideal near the vertex
  set y : (ReesAlg (compFil hI hmax h𝔭 d)) := ⟨LaurentPolynomial.C f * T j, C_mul_T_mem_ReesAlg hf⟩
  have hy₀ : algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Localization.AtPrime P₀) y ∈
      (ck.RF ek (1 / d)).map (Loc.map (hctrl P₀ hg)) := by
    rw [Loc.map_RF, ← (hbound' P₀ hg J₀ hJ₀adm).2 (by rw [hJ₀e, hek]) (1 / d)]
    exact hJ₀homog j hj f hf
  obtain ⟨h, hh, hhy⟩ := Loc.exists_of_mem_map (hctrl P₀ hg) _ hy₀
  -- choose a rescaling moving `P` into `D(g h)`
  set G := g * h
  have hG : hcomp (compFil hI hmax h𝔭 d) G 0 ∉ P := by
    intro hGP
    have hGP₀ : G ∉ P₀ := fun h' => (Ideal.IsPrime.mem_or_mem inferInstance h').elim hg hh
    apply hGP₀
    rw [mem_vertexG]
    have : hcomp (compFil hI hmax h𝔭 d) G 0 = algebraMap A (ReesAlg (compFil hI hmax h𝔭 d)) ((G : A[T;T⁻¹]).coeff 0) := by
      apply Subtype.ext
      show LaurentPolynomial.C ((G : A[T;T⁻¹]).coeff 0) * T 0 = _
      rw [T_zero, mul_one, LaurentPolynomial.C_eq_algebraMap]; rfl
    rw [this] at hGP
    exact hGP
  obtain ⟨μ, hμ, hμG⟩ := exists_reesScale_not_mem (compFil hI hmax h𝔭 d) hneg P hsP G hG
  set σ := reesScale (compFil hI hmax h𝔭 d) (qUnit (B := A) μ hμ)
  set P' := P.comap σ
  haveI : P'.IsMaximal := Ideal.comap_isMaximal_of_surjective σ σ.surjective
  have hgP' : g ∉ P' := fun h' => hμG (by rw [Ideal.mem_comap] at h'; exact
    (show σ G ∈ P by rw [map_mul]; exact P.mul_mem_right _ h'))
  have hhP' : h ∉ P' := fun h' => hμG (by rw [Ideal.mem_comap] at h'; exact
    (show σ G ∈ P by rw [map_mul]; exact P.mul_mem_left _ h'))
  have hIwP' : (weakT (compFil hI hmax h𝔭 d) I d hId) ≤ P' := by
    intro x hx
    rw [Ideal.mem_comap]
    exact hIwP ((reesScale_weakT_le (compFil hI hmax h𝔭 d) _ d hId) (Ideal.mem_map_of_mem _ hx))
  -- the invariant at `P'`
  obtain ⟨v', hv'⟩ := exists_invAt hIw0 P' hIwP'
  have hvv : v = v' := by
    refine hv.unique ?_
    exact InvAt.of_ringEquiv σ (reesScale_weakT (compFil hI hmax h𝔭 d) _ d hId) P hv'
  subst hvv
  obtain ⟨n'', e', he', rfl⟩ := hv'
  obtain rfl := he'.card_eq (Loc.transport (hctrl P' hgP') ck)
  obtain ⟨⟨J', hJ', hJ'e⟩, hmin'⟩ := he'
  have hle := (hbound' P' hgP' J' hJ').1
  rw [hJ'e, hek] at hle
  rcases hle.lt_or_eq with hlt | heq
  · have := ext0_lt hlt
    rwa [ext0_pad (by omega), D.hev] at this
  · exfalso
    -- equality forces `y ∈ P'`, hence `y ∈ P`
    have hRF := (hbound' P' hgP' J' hJ').2 (by rw [hJ'e, hek]; exact (toLex.injective heq).symm)
    have hmem : algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Localization.AtPrime P') (h * y) ∈ J'.RF (1 / d) := by
      rw [hRF (1 / d), ← Loc.map_RF, ← Loc.map_algebraMap (hctrl P' hgP')]
      exact Ideal.mem_map_of_mem _ hhy
    have hmax' := J'.centred.RF_le_maximalIdeal (show (0 : ℚ) < 1 / d by positivity) hmem
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ P'] at hmax'
    have hyP' : y ∈ P' := ((Ideal.IsPrime.mem_or_mem inferInstance hmax').resolve_left hhP')
    rw [Ideal.mem_comap] at hyP'
    apply hyP
    have : σ y = algebraMap A (ReesAlg (compFil hI hmax h𝔭 d)) ↑((qUnit (B := A) μ hμ) ^ j) * y := by
      apply Subtype.ext
      rw [reesScale_coe]
      show lscale _ (LaurentPolynomial.C f * T j) =
        algebraMap A A[T;T⁻¹] ↑((qUnit (B := A) μ hμ) ^ j) * (LaurentPolynomial.C f * T j)
      rw [lscale_C_mul_T, ← LaurentPolynomial.C_eq_algebraMap, ← mul_assoc, ← map_mul, mul_comm f]
    rw [this] at hyP'
    refine ((Ideal.IsPrime.mem_or_mem inferInstance hyP').resolve_left fun hu => ?_)
    have hunit : IsUnit (algebraMap A (ReesAlg (compFil hI hmax h𝔭 d)) ↑((qUnit (B := A) μ hμ) ^ j)) :=
      (Units.isUnit _).map _
    exact hPm.ne_top (Ideal.eq_top_of_isUnit_mem _ hu hunit)

end BezoutCounterexample.Principalization

