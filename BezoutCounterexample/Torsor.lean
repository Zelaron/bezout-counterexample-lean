import BezoutCounterexample.Divisorial

/-!
# Section 4.2: the torsor step (Lemmas 4.2 and 4.3)

Assume `k ≥ 2`. Let `h = (h₀, h₁, …, h_ℓ) = (πT, g T^j : g ∈ G_j, 1 ≤ j ≤ d)` be the tuple of
elements of `𝓡₊` obtained by listing `πT` followed by the elements `g T^j` with `g ∈ G_j`,
`1 ≤ j ≤ d`; write `hᵢ = gᵢ T^{jᵢ}` with `1 ≤ jᵢ ≤ d` and `gᵢ ∈ 𝓕_{jᵢ}` (so `g₀ = π`, `j₀ = 1`).
By Lemma 3.5(2) the entries of `h` generate `𝓡₊` (`PrincipalizationData.span_h`). Put
`U = J_𝓡(h) = 𝓡[σ₀, …, σ_ℓ]/(∑ hᵢσᵢ - 1)`, the Jouanolou affine-space bundle over
`Spec 𝓡 ∖ V(𝓡₊)`, and `I₁ = I_w U`.

* **Lemma 4.2** (`lem:torsor`): `U` is a smooth finitely generated factorial `ℚ`-domain, `A → U` is
  injective, `s` is a prime element of `U`, and `IU = s^d I₁` (`torsor_spec`).
* **Lemma 4.3** (`lem:torsor-invariant`): `torsor_invariant`.
-/

noncomputable section

namespace BezoutCounterexample

open IsLocalRing Principalization LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [UniqueFactorizationMonoid A]

namespace PrincipalizationData

variable (S : PrincipalizationData A)

theorem π_mem_fil : S.π ∈ S.fil.F 1 := by
  rw [S.fil_F, S.𝓕_one]; exact S.π_mem

theorem π_ne_zero : S.π ≠ 0 := S.prime_π.ne_zero

/-- `ℓ`: the tuple `h` has `ℓ + 1` entries. -/
abbrev ℓ : ℕ := nGen S.ne_bot S.hmax S.h𝔭 S.d

/-- The tuple `h = (πT, g T^j : g ∈ G_j, 1 ≤ j ≤ d)` of elements of `𝓡₊`. -/
abbrev h : Fin (S.ℓ + 1) → S.𝓡 := torsorY S.ne_bot S.hmax S.h𝔭 S.d S.π_mem_fil

/-- The degrees `jᵢ`. -/
def jdeg (i : Fin (S.ℓ + 1)) : ℕ := (genDeg S.ne_bot S.hmax S.h𝔭 S.d i).toNat

/-- The coefficients `gᵢ`. -/
def g (i : Fin (S.ℓ + 1)) : A := genCoeff S.ne_bot S.hmax S.h𝔭 S.d S.π i

/-- `hᵢ = gᵢ T^{jᵢ}` with `1 ≤ jᵢ ≤ d` and `gᵢ ∈ 𝓕_{jᵢ}`. -/
theorem h_spec (i : Fin (S.ℓ + 1)) :
    (S.h i : A[T;T⁻¹]) = C (S.g i) * T (S.jdeg i) ∧ 1 ≤ S.jdeg i ∧ S.jdeg i ≤ S.d ∧
      S.g i ∈ S.𝓕 (S.jdeg i) := by
  have h1 := genDeg_pos S.ne_bot S.hmax S.h𝔭 S.d i
  have h2 := genDeg_le S.ne_bot S.hmax S.h𝔭 S.d S.one_le_d i
  have hj : ((S.jdeg i : ℕ) : ℤ) = genDeg S.ne_bot S.hmax S.h𝔭 S.d i := by
    simp only [jdeg]; omega
  refine ⟨?_, by omega, by omega, ?_⟩
  · rw [hj]; rfl
  · rw [hj, ← S.fil_F]; exact genCoeff_mem S.ne_bot S.hmax S.h𝔭 S.d S.π_mem_fil i

/-- `h₀ = πT`: `g₀ = π` and `j₀ = 1`. -/
theorem h_zero : S.g 0 = S.π ∧ S.jdeg 0 = 1 := by
  refine ⟨by simp [PrincipalizationData.g, genCoeff], by simp [jdeg, genDeg]⟩

/-- The entries `h₁, …, h_ℓ` are the elements `g T^j` with `g ∈ G_j` and `1 ≤ j ≤ d`. -/
theorem h_succ (i : Fin S.ℓ) : S.g i.succ ∈ S.G (S.jdeg i.succ) := by
  have hmem := genPairs_mem S.ne_bot S.hmax S.h𝔭 S.d
    (List.get_mem (genPairs S.ne_bot S.hmax S.h𝔭 S.d) i)
  have hj : ((S.jdeg i.succ : ℕ) : ℤ) = ((genPairs S.ne_bot S.hmax S.h𝔭 S.d).get i).1 := by
    simp only [jdeg, genDeg, Fin.cons_succ]; omega
  rw [hj]
  simpa [PrincipalizationData.g, genCoeff, ReesData.G] using hmem.2.2

theorem exists_h_eq {j : ℤ} (hj1 : 1 ≤ j) (hjd : j ≤ S.d) {g : A} (hg : g ∈ S.G j) :
    ∃ i : Fin S.ℓ, (S.jdeg i.succ : ℤ) = j ∧ S.g i.succ = g := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.1 (mem_genPairs S.ne_bot S.hmax S.h𝔭 S.d hj1 hjd hg)
  refine ⟨i, ?_, ?_⟩
  · simp only [jdeg, genDeg, Fin.cons_succ, hi]; omega
  · simp only [PrincipalizationData.g, genCoeff, Fin.cons_succ, hi]

/-- By Lemma 3.5(2), the entries of `h` generate `𝓡₊`. -/
theorem span_h : Ideal.span (Set.range S.h) = S.𝓡plus := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨hh, h1, -, hg⟩ := S.h_spec i
    exact Ideal.subset_span ⟨S.jdeg i, S.g i, by exact_mod_cast h1, hg, hh⟩
  · rw [S.𝓡plus_eq_span, Ideal.span_le]
    rintro r ⟨j, hj, g, hg, hr⟩
    obtain ⟨i, hij, hig⟩ := S.exists_h_eq (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2 hg
    have : r = S.h i.succ := Subtype.ext (by rw [hr, (S.h_spec i.succ).1, hij, hig])
    rw [this]
    exact Ideal.subset_span ⟨i.succ, rfl⟩

/-- The torsor `U = J_𝓡(h)`. -/
abbrev U : Type := Jou.J S.h

/-- The exceptional element `s` in `U`. -/
def sU : S.U := algebraMap S.𝓡 S.U S.s

/-- `I₁ = I_w U`. -/
def I₁ : Ideal S.U := S.Iw.map (algebraMap S.𝓡 S.U)

instance isDomain_U : IsDomain S.U :=
  torsor_isDomain S.ne_bot S.hmax S.h𝔭 S.π_mem_fil S.π_ne_zero

instance smooth_U : Algebra.Smooth ℚ S.U :=
  torsor_smooth S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw S.π_mem_fil

/-! ## Lemma 4.2 -/

/-- **Lemma 4.2** (`lem:torsor`): `U` is a smooth finitely generated factorial `ℚ`-domain, the
homomorphism `A → U` is injective, `s` is a prime element of `U`, and `IU = s^d I₁`. -/
theorem torsor_spec (hk : 2 ≤ S.k) :
    IsDomain S.U ∧ Algebra.Smooth ℚ S.U ∧ UniqueFactorizationMonoid S.U ∧
      Function.Injective (algebraMap A S.U) ∧ Prime S.sU ∧
      S.I.map (algebraMap A S.U) = Ideal.span {S.sU ^ S.d} * S.I₁ := by
  have hk2 : maxinv S.I 1 ≠ 0 := (S.e_ne_zero_iff 1).2 (by omega)
  exact ⟨inferInstance, inferInstance,
    torsor_ufd S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw S.π_mem_fil hk2 S.prime_π S.π_mem,
    torsor_injective S.ne_bot S.hmax S.h𝔭 S.π_mem_fil S.π_ne_zero,
    torsor_s_prime S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw S.π_mem_fil S.π_ne_zero,
    torsor_map_eq S.ne_bot S.hmax S.h𝔭 S.d_pos S.π_mem_fil⟩

/-- `U` as a smooth finitely generated factorial `ℚ`-domain (Lemma 4.2). -/
def torsorSFD (hk : 2 ≤ S.k) : SmoothFactorialDomain where
  carrier := S.U
  ufd := (S.torsor_spec hk).2.2.1

/-! ## Lemma 4.3 -/

/-- **Lemma 4.3** (`lem:torsor-invariant`). The ideal `I₁` is nonzero. Let `Q ⊇ I₁` be a maximal
ideal of `U` and `P = Q ∩ 𝓡`.
1. If `s ∈ Q`, then `inv_Q(I₁) = inv_P(I_w) ≺ maxinv(I)`.
2. If `s ∉ Q`, then `𝔮 = Q ∩ A` is a maximal ideal of `A` that contains `I` but not `𝔭`, and
   `inv_Q(I₁) = inv_𝔮(I)`.

Consequently, either `maxinv(I₁) ≺ maxinv(I)` or `I₁ = U`, or `maxinv(I₁) = maxinv(I)` and the
components of the maximal locus of `I₁` are the `V(𝔭'U)`, where `V(𝔭')` ranges over the components
of the maximal locus of `I` other than `V(𝔭)`; in particular `c(I₁) < c(I)`. -/
theorem torsor_invariant (hk : 2 ≤ S.k) :
    S.I₁ ≠ ⊥ ∧
    (∀ (Q : Ideal S.U) [Q.IsMaximal], S.I₁ ≤ Q → S.sU ∈ Q →
      (Q.comap (algebraMap S.𝓡 S.U)).IsMaximal ∧
      inv S.I₁ Q = inv S.Iw (Q.comap (algebraMap S.𝓡 S.U)) ∧
      inv S.Iw (Q.comap (algebraMap S.𝓡 S.U)) ≺ maxinv S.I) ∧
    (∀ (Q : Ideal S.U) [Q.IsMaximal], S.I₁ ≤ Q → S.sU ∉ Q →
      (Q.comap (algebraMap A S.U)).IsMaximal ∧ S.I ≤ Q.comap (algebraMap A S.U) ∧
      ¬ S.𝔭 ≤ Q.comap (algebraMap A S.U) ∧
      inv S.I₁ Q = inv S.I (Q.comap (algebraMap A S.U))) ∧
    (maxinv S.I₁ ≺ maxinv S.I ∨ S.I₁ = ⊤ ∨
      (maxinv S.I₁ = maxinv S.I ∧
        components S.I₁ = (fun 𝔭' => 𝔭'.map (algebraMap A S.U)) '' (components S.I \ {S.𝔭}) ∧
        numComponents S.I₁ < numComponents S.I)) := by
  have hI₁ : S.I₁ ≠ ⊥ := torsorI_ne_bot S.ne_bot S.hmax S.h𝔭 S.d_pos S.π_mem_fil S.π_ne_zero
  have hIw0 : S.Iw ≠ ⊥ := weakT_ne_bot S.fil S.ne_bot S.d S.I_le_fil
  -- (1) points on the exceptional divisor: smooth invariance and Theorem 3.6
  have part1 : ∀ (Q : Ideal S.U) [Q.IsMaximal], S.I₁ ≤ Q → S.sU ∈ Q →
      (Q.comap (algebraMap S.𝓡 S.U)).IsMaximal ∧
      inv S.I₁ Q = inv S.Iw (Q.comap (algebraMap S.𝓡 S.U)) ∧
      inv S.Iw (Q.comap (algebraMap S.𝓡 S.U)) ≺ maxinv S.I := by
    intro Q _ hIQ hsQ
    have hPmax : (Q.comap (algebraMap S.𝓡 S.U)).IsMaximal := comap_isMaximal_of_finiteType Q
    have hIwP : S.Iw ≤ Q.comap (algebraMap S.𝓡 S.U) := Ideal.map_le_iff_le_comap.1 hIQ
    -- some `hᵢ` is a unit at `Q`, since `∑ hᵢ σᵢ = 1`
    obtain ⟨l, hl⟩ := exists_torsorY_not_mem S.ne_bot S.hmax S.h𝔭 S.π_mem_fil Q
    have hinvQ := invAt_torsor_of_rees S.h Q hl hIw0 hIwP (invAt_inv hIw0 hIwP)
    refine ⟨hPmax, inv_eq_of_invAt hI₁ hIQ hinvQ, ?_⟩
    refine S.drop _ hIwP hsQ fun hle => hl (hle ?_)
    rw [← S.span_h]
    exact Ideal.subset_span ⟨l, rfl⟩
  -- (2) points off the exceptional divisor
  have part2 : ∀ (Q : Ideal S.U) [Q.IsMaximal], S.I₁ ≤ Q → S.sU ∉ Q →
      (Q.comap (algebraMap A S.U)).IsMaximal ∧ S.I ≤ Q.comap (algebraMap A S.U) ∧
      ¬ S.𝔭 ≤ Q.comap (algebraMap A S.U) ∧
      inv S.I₁ Q = inv S.I (Q.comap (algebraMap A S.U)) := by
    intro Q _ hIQ hsQ
    rcases torsor_invAt S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw S.π_mem_fil S.π_ne_zero Q hIQ
      (invAt_inv hI₁ hIQ) with ⟨hs, -⟩ | ⟨-, hI𝔮, h𝔭𝔮, hv⟩
    · exact absurd hs hsQ
    · have h𝔮 : (Q.comap (algebraMap A S.U)).IsMaximal := comap_isMaximal_of_finiteType Q
      exact ⟨h𝔮, hI𝔮, h𝔭𝔮, (inv_eq_of_invAt S.ne_bot hI𝔮 hv).symm⟩
  refine ⟨hI₁, part1, part2, ?_⟩
  -- the consequence
  by_cases htop : S.I₁ = ⊤
  · exact Or.inr (Or.inl htop)
  obtain ⟨⟨Q₁, hQ₁, hIQ₁, hinv₁⟩, -⟩ := maxinv_spec hI₁ htop
  have hle : maxinv S.I₁ ⪯ maxinv S.I := by
    rw [← hinv₁]
    exact torsor_inv_ge S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw S.π_mem_fil S.π_ne_zero Q₁ hIQ₁
      (invAt_inv hI₁ hIQ₁)
  by_cases heq : maxinv S.I₁ = maxinv S.I
  swap
  · exact Or.inl ⟨hle, heq⟩
  obtain ⟨hfin, hprime, hcomax, hiff, -⟩ := theorem_3_3_3 S.ne_bot S.ne_top
  have : IsJacobsonRing S.U := isJacobsonRing_of_finiteType (A := ℚ)
  -- maximal ideals over another component `𝔭'` avoid `s`
  have hsnot : ∀ 𝔭' ∈ components S.I, 𝔭' ≠ S.𝔭 → ∀ Q : Ideal S.U, Q.IsMaximal →
      𝔭'.map (algebraMap A S.U) ≤ Q → S.sU ∉ Q := by
    intro 𝔭' h𝔭' hne Q hQ hle' hsQ
    have h1 : S.𝔭.map (algebraMap A S.U) ≤ Q := by
      rw [IsScalarTower.algebraMap_eq A S.𝓡 S.U, ← Ideal.map_map]
      refine (Ideal.map_mono S.map_𝔭_le).trans ?_
      rw [Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
      exact hsQ
    have h2 : (S.𝔭 ⊔ 𝔭').map (algebraMap A S.U) ≤ Q := by
      rw [Ideal.map_sup]; exact sup_le h1 hle'
    rw [hcomax S.𝔭 S.mem_components 𝔭' h𝔭' (Ne.symm hne), Ideal.map_top] at h2
    exact hQ.ne_top (top_le_iff.1 h2)
  have hmapI := (S.torsor_spec hk).2.2.2.2.2
  -- `I₁ ⊆ Q` for maximal `Q ⊇ 𝔭' U`
  have hI₁Q : ∀ 𝔭' ∈ components S.I, 𝔭' ≠ S.𝔭 → ∀ Q : Ideal S.U, Q.IsMaximal →
      𝔭'.map (algebraMap A S.U) ≤ Q → S.I₁ ≤ Q := by
    intro 𝔭' h𝔭' hne Q hQ hle'
    have hsQ := hsnot 𝔭' h𝔭' hne Q hQ hle'
    have h1 : Ideal.span {S.sU ^ S.d} * S.I₁ ≤ Q := by
      rw [← hmapI]
      exact (Ideal.map_mono ((hprime 𝔭' h𝔭').2)).trans hle'
    rcases hQ.isPrime.mul_le.1 h1 with h | h
    · rw [Ideal.span_le, Set.singleton_subset_iff] at h
      exact absurd (hQ.isPrime.mem_of_pow_mem _ h) hsQ
    · exact h
  have hcomp : components S.I₁ =
      (fun 𝔭' => 𝔭'.map (algebraMap A S.U)) '' (components S.I \ {S.𝔭}) := by
    refine components_eq_of hI₁ htop (hfin.sdiff.image _) ?_ ?_ ?_
    · rintro _ ⟨𝔭', ⟨h𝔭', hne⟩, rfl⟩
      have hne' : 𝔭' ≠ S.𝔭 := hne
      have h𝔭'min : 𝔭' ∈ (locusIdeal S.I (maxinv S.I)).minimalPrimes := by
        rw [← maxLocusIdeal_eq_locusIdeal S.ne_bot]; exact h𝔭'
      have hP := torsor_comp_isPrime S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw S.π_mem_fil
        h𝔭'min (Ne.symm hne')
      have hP' : (𝔭'.map (algebraMap A S.U)).IsPrime := hP
      refine ⟨hP', ?_⟩
      show S.I₁ ≤ 𝔭'.map (algebraMap A S.U)
      rw [← IsJacobsonRing.out' _ hP'.isRadical, Ideal.jacobson]
      exact le_sInf fun Q ⟨hle', hQ⟩ => hI₁Q 𝔭' h𝔭' hne' Q hQ hle'
    · rintro _ ⟨𝔭', ⟨h𝔭', hne⟩, rfl⟩ _ ⟨𝔭'', ⟨h𝔭'', hne'⟩, rfl⟩ hPQ
      have h' : 𝔭' ≠ 𝔭'' := fun h => hPQ (by rw [h])
      rw [← Ideal.map_sup, hcomax 𝔭' h𝔭' 𝔭'' h𝔭'' h', Ideal.map_top]
    · intro Q _ hIQ
      rw [heq]
      constructor
      · intro hinvQ
        by_cases hsQ : S.sU ∈ Q
        · exfalso
          obtain ⟨-, h1, h2⟩ := part1 Q hIQ hsQ
          rw [← h1, hinvQ] at h2
          exact h2.2 rfl
        · obtain ⟨h𝔮, hI𝔮, h𝔭𝔮, hinv⟩ := part2 Q hIQ hsQ
          rw [hinv] at hinvQ
          obtain ⟨𝔭', h𝔭', h𝔭'𝔮⟩ := (hiff _ hI𝔮).1 hinvQ
          refine ⟨𝔭'.map (algebraMap A S.U), ⟨𝔭', ⟨h𝔭', fun h => h𝔭𝔮 ?_⟩, rfl⟩,
            Ideal.map_le_iff_le_comap.2 h𝔭'𝔮⟩
          rw [Set.mem_singleton_iff] at h
          rwa [← h]
      · rintro ⟨_, ⟨𝔭', ⟨h𝔭', hne⟩, rfl⟩, hle'⟩
        have hsQ := hsnot 𝔭' h𝔭' hne Q inferInstance hle'
        obtain ⟨h𝔮, hI𝔮, -, hinv⟩ := part2 Q hIQ hsQ
        rw [hinv]
        exact (hiff _ hI𝔮).2 ⟨𝔭', h𝔭', Ideal.map_le_iff_le_comap.1 hle'⟩
  refine Or.inr (Or.inr ⟨heq, hcomp, ?_⟩)
  unfold numComponents
  rw [hcomp]
  exact (Set.ncard_image_le hfin.sdiff).trans_lt
    (Set.ncard_sdiff_singleton_lt_of_mem S.mem_components hfin)

end PrincipalizationData

end BezoutCounterexample
