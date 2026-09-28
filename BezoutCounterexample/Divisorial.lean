import BezoutCounterexample.Rees

/-!
# Section 4: the setting, and the divisorial step (Lemma 4.1)

Throughout Section 4, `A` is a smooth finitely generated factorial `ℚ`-domain and `I ⊊ A` is a
nonzero ideal. We fix a component `V(𝔭)` of the maximal locus of `I` and use Notation 3.4; `k ≥ 1`
is the number of nonzero entries of `e = maxinv(I)`. Since `A` is a UFD and `𝔭 ≠ 0`, `𝔭` contains a
prime element `π`. This data is bundled as `PrincipalizationData A`; `numComponents I = c(I)`.

One step replaces `(A, I)` by a pair `(B, I₁)`, where `B = A` or `B ⊇ A` is again a smooth
finitely generated factorial `ℚ`-domain, and factors `IB = α I₁`; the complexity decreases: either
`I₁ = B`, or `maxinv(I₁) ≺ maxinv(I)`, or `maxinv(I₁) = maxinv(I)` and `c(I₁) < c(I)`. The divisorial
case `k = 1` is **Lemma 4.1** (`lem:divisorial`), below; the case `k ≥ 2` is the torsor step
(`Torsor.lean`).
-/

noncomputable section

namespace BezoutCounterexample

open IsLocalRing Principalization

/-- The setting of Section 4: Notation 3.4 for a smooth finitely generated factorial `ℚ`-domain
`A`, together with a prime element `π ∈ 𝔭`. -/
structure PrincipalizationData (A : Type) [CommRing A] [IsDomain A] [Algebra ℚ A]
    [Algebra.Smooth ℚ A] [UniqueFactorizationMonoid A] extends ReesData A where
  /-- A prime element `π ∈ 𝔭`. -/
  π : A
  prime_π : Prime π
  π_mem : π ∈ 𝔭

/-! ## Components are determined by the maximal locus -/

/-- In a Jacobson ring, two finite families of pairwise comaximal primes with the same maximal
ideals above them coincide. -/
theorem eq_of_forall_isMaximal {R : Type*} [CommRing R] [IsJacobsonRing R]
    {F G : Set (Ideal R)} (hF : F.Finite) (hG : G.Finite) (hFp : ∀ P ∈ F, P.IsPrime)
    (hGp : ∀ P ∈ G, P.IsPrime) (hFc : ∀ P ∈ F, ∀ Q ∈ F, P ≠ Q → P ⊔ Q = ⊤)
    (hGc : ∀ P ∈ G, ∀ Q ∈ G, P ≠ Q → P ⊔ Q = ⊤)
    (h : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → ((∃ P ∈ F, P ≤ 𝔪) ↔ (∃ Q ∈ G, Q ≤ 𝔪))) : F = G := by
  classical
  -- for `P` in one family, some member of the other family lies below `P`
  have below : ∀ {F G : Set (Ideal R)}, G.Finite → (∀ P ∈ F, P.IsPrime) →
      (∀ 𝔪 : Ideal R, 𝔪.IsMaximal → ((∃ P ∈ F, P ≤ 𝔪) → (∃ Q ∈ G, Q ≤ 𝔪))) →
      ∀ P ∈ F, ∃ Q ∈ G, Q ≤ P := by
    intro F G hG hFp h P hP
    have := hFp P hP
    have hprod : hG.toFinset.prod id ≤ P := by
      rw [← (IsJacobsonRing.out' P (hFp P hP).isRadical)]
      refine le_sInf fun 𝔪 ⟨hP𝔪, h𝔪⟩ => ?_
      obtain ⟨Q, hQ, hQ𝔪⟩ := h 𝔪 h𝔪 ⟨P, hP, hP𝔪⟩
      exact (Ideal.prod_le_inf.trans (Finset.inf_le (hG.mem_toFinset.2 hQ))).trans hQ𝔪
    obtain ⟨Q, hQ, hQP⟩ := (Ideal.IsPrime.prod_le (hFp P hP)).1 hprod
    exact ⟨Q, hG.mem_toFinset.1 hQ, hQP⟩
  have sub : ∀ {F G : Set (Ideal R)}, F.Finite → G.Finite → (∀ P ∈ F, P.IsPrime) →
      (∀ P ∈ G, P.IsPrime) → (∀ P ∈ F, ∀ Q ∈ F, P ≠ Q → P ⊔ Q = ⊤) →
      (∀ 𝔪 : Ideal R, 𝔪.IsMaximal → ((∃ P ∈ F, P ≤ 𝔪) ↔ (∃ Q ∈ G, Q ≤ 𝔪))) → F ⊆ G := by
    intro F G hF hG hFp hGp hFc h P hP
    obtain ⟨Q, hQ, hQP⟩ := below hG hFp (fun 𝔪 h𝔪 => (h 𝔪 h𝔪).1) P hP
    obtain ⟨P', hP', hP'Q⟩ := below hF hGp (fun 𝔪 h𝔪 => (h 𝔪 h𝔪).2) Q hQ
    have hPP' : P' = P := by
      by_contra hne
      have := hFc P' hP' P hP hne
      rw [sup_eq_right.2 (hP'Q.trans hQP)] at this
      exact (hFp P hP).ne_top this
    rw [hPP'] at hP'Q
    rwa [le_antisymm hQP hP'Q] at hQ
  exact le_antisymm (sub hF hG hFp hGp hFc h) (sub hG hF hGp hFp hGc fun 𝔪 h𝔪 => (h 𝔪 h𝔪).symm)

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

/-- The components of the maximal locus are determined by the maximal locus: a finite family of
pairwise comaximal primes containing `I` over which the maximal ideals `𝔪 ⊇ I` with
`inv_𝔪(I) = maxinv(I)` are exactly those containing a member of the family is `components I`. -/
theorem components_eq_of {I : Ideal A} (hI : I ≠ ⊥) (hItop : I ≠ ⊤) {F : Set (Ideal A)}
    (hF : F.Finite) (hFp : ∀ P ∈ F, P.IsPrime ∧ I ≤ P)
    (hFc : ∀ P ∈ F, ∀ Q ∈ F, P ≠ Q → P ⊔ Q = ⊤)
    (hloc : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 →
      (inv I 𝔪 = maxinv I ↔ ∃ P ∈ F, P ≤ 𝔪)) :
    components I = F := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℚ)
  obtain ⟨hfin, hprime, hcomax, hiff, -⟩ := theorem_3_3_3 hI hItop
  refine eq_of_forall_isMaximal hfin hF (fun P hP => (hprime P hP).1) (fun P hP => (hFp P hP).1)
    hcomax hFc fun 𝔪 h𝔪 => ?_
  by_cases hI𝔪 : I ≤ 𝔪
  · exact (hiff 𝔪 hI𝔪).symm.trans (hloc 𝔪 hI𝔪)
  · constructor
    · rintro ⟨P, hP, hP𝔪⟩; exact absurd ((hprime P hP).2.trans hP𝔪) hI𝔪
    · rintro ⟨P, hP, hP𝔪⟩; exact absurd ((hFp P hP).2.trans hP𝔪) hI𝔪

/-- The first weight of `maxinv(I)` is `1/a` for a positive integer `a`. -/
theorem exists_maxinv_zero_eq {I : Ideal A} (hI : I ≠ ⊥) (hItop : I ≠ ⊤) :
    ∃ a : ℕ, 0 < a ∧ maxinv I 0 = 1 / a := by
  obtain ⟨⟨𝔪, h𝔪, hI𝔪, hinv⟩, -⟩ := maxinv_spec hI hItop
  rw [← hinv]; exact exists_inv_zero_eq hI hI𝔪

theorem ReesData.e_ne_zero_iff (S : ReesData A) (i : ℕ) : S.e i ≠ 0 ↔ i < S.k :=
  ne_zero_iff_lt_numNonzero (maxinv_mem_Γ S.ne_bot S.ne_top)
    (finite_support_maxinv S.ne_bot S.ne_top) i

/-- `k ≥ 1`: the first weight of `maxinv(I)` is nonzero. -/
theorem ReesData.one_le_k (S : ReesData A) : 1 ≤ S.k := by
  obtain ⟨a, ha, he⟩ := exists_maxinv_zero_eq S.ne_bot S.ne_top
  have h0 : S.e 0 ≠ 0 := by
    show maxinv S.I 0 ≠ 0
    rw [he]; positivity
  exact (S.e_ne_zero_iff 0).1 h0

variable [UniqueFactorizationMonoid A]

/-- Given Notation 3.4 over a UFD, a prime element `π ∈ 𝔭` exists. -/
theorem ReesData.exists_prime_mem (S : ReesData A) : ∃ π : A, Prime π ∧ π ∈ S.𝔭 := by
  have h𝔭 := (theorem_3_3_3 S.ne_bot S.ne_top).2.1 S.𝔭 S.mem_components
  have hne : S.𝔭 ≠ ⊥ := fun h => S.ne_bot (eq_bot_iff.2 (h ▸ h𝔭.2))
  obtain ⟨π, hπ𝔭, hπ⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot h𝔭.1 hne
  exact ⟨π, hπ, hπ𝔭⟩

namespace PrincipalizationData

variable (S : PrincipalizationData A)

/-! ## Lemma 4.1: the divisorial step -/

/-- The ideal `I₁ = (I : π^a)` of the divisorial step. -/
def divI₁ (a : ℕ) : Ideal A := S.I.colon {S.π ^ a}

section Divisorial

variable (hk : S.k = 1)
include hk

/-- **Lemma 4.1**: if `k = 1`, then `e = (1/a, 0, 0, …)` for a positive integer `a`
(Theorem 3.3(1)). -/
theorem divisorial_e : ∃ a : ℕ, 0 < a ∧ S.e = fun i => if i = 0 then 1 / (a : ℚ) else 0 := by
  obtain ⟨a, ha, he⟩ := exists_maxinv_zero_eq S.ne_bot S.ne_top
  refine ⟨a, ha, funext fun i => ?_⟩
  split_ifs with hi
  · subst hi; exact he
  · by_contra h
    have := (S.e_ne_zero_iff i).1 h
    have hk' : S.toReesData.k = 1 := hk
    omega

theorem e_zero_ne : S.e 0 ≠ 0 := (S.e_ne_zero_iff 0).2 (by have : S.toReesData.k = 1 := hk; omega)

theorem e_one_eq : S.e 1 = 0 := by
  by_contra h
  have := (S.e_ne_zero_iff 1).1 h
  have hk' : S.toReesData.k = 1 := hk
  omega

/-- **Lemma 4.1**: `𝔭 = π A`. -/
theorem divisorial_𝔭_eq : S.𝔭 = Ideal.span {S.π} :=
  div_eq_span S.ne_bot S.hmax S.h𝔭 (S.e_zero_ne hk) (S.e_one_eq hk) S.prime_π S.π_mem

variable {a : ℕ} (ha : S.e 0 = 1 / (a : ℚ))
include ha

/-- **Lemma 4.1**: `I ⊆ π^a A`. -/
theorem divisorial_le : S.I ≤ Ideal.span {S.π ^ a} :=
  div_le_span_pow S.ne_bot S.hmax S.h𝔭 S.d_pos (S.e_zero_ne hk) (S.e_one_eq hk) S.prime_π
    S.π_mem ha

theorem a_pos : 0 < a := by
  rcases Nat.eq_zero_or_pos a with h | h
  · exfalso; apply S.e_zero_ne hk; rw [ha, h]; simp
  · exact h

/-- **Lemma 4.1**: `I = π^a I₁`, `I₁ = (I : π^a)`. -/
theorem divisorial_I_eq : S.I = Ideal.span {S.π ^ a} * S.divI₁ a :=
  div_eq_mul (S.divisorial_le hk ha)

/-- **Lemma 4.1**: `I₁ + π A = A`. -/
theorem divisorial_sup : S.divI₁ a ⊔ Ideal.span {S.π} = ⊤ := by
  by_contra h
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ h
  exact div_not_mem S.ne_bot S.hmax (S.a_pos hk ha) ha (S.divisorial_le hk ha) 𝔪
    (le_sup_left.trans hle) (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self S.π)))

/-- A maximal ideal containing `I₁` does not contain `π`. -/
theorem π_not_mem (𝔪 : Ideal A) [𝔪.IsMaximal] (h𝔪 : S.divI₁ a ≤ 𝔪) : S.π ∉ 𝔪 :=
  div_not_mem S.ne_bot S.hmax (S.a_pos hk ha) ha (S.divisorial_le hk ha) 𝔪 h𝔪

/-- **Lemma 4.1**: `inv_𝔪(I₁) = inv_𝔪(I)` for every maximal ideal `𝔪 ⊇ I₁`. -/
theorem divisorial_inv_eq (𝔪 : Ideal A) [𝔪.IsMaximal] (h𝔪 : S.divI₁ a ≤ 𝔪) :
    inv (S.divI₁ a) 𝔪 = inv S.I 𝔪 := by
  have hI𝔪 : S.I ≤ 𝔪 := (le_divI S.I S.π a).trans h𝔪
  exact inv_eq_of_invAt (divI_ne_bot S.ne_bot) h𝔪
    ((div_invAt_iff S.ne_bot S.hmax (S.a_pos hk ha) ha (S.divisorial_le hk ha) 𝔪 h𝔪).2
      (invAt_inv S.ne_bot hI𝔪))

/-- **Lemma 4.1**: either `maxinv(I₁) ≺ maxinv(I)` or `I₁ = A`, or `maxinv(I₁) = maxinv(I)` and the
components of the maximal locus of `I₁` are those of `I` other than `V(𝔭)`; in particular
`c(I₁) < c(I)`. -/
theorem divisorial_decrease :
    maxinv (S.divI₁ a) ≺ maxinv S.I ∨ S.divI₁ a = ⊤ ∨
      (maxinv (S.divI₁ a) = maxinv S.I ∧ components (S.divI₁ a) = components S.I \ {S.𝔭} ∧
        numComponents (S.divI₁ a) < numComponents S.I) := by
  by_cases htop : S.divI₁ a = ⊤
  · exact Or.inr (Or.inl htop)
  have hI₁ : S.divI₁ a ≠ ⊥ := divI_ne_bot S.ne_bot
  have hII₁ : S.I ≤ S.divI₁ a := le_divI S.I S.π a
  -- `maxinv(I₁) ⪯ maxinv(I)`
  obtain ⟨⟨𝔪₁, h𝔪₁, hI₁𝔪₁, hinv₁⟩, -⟩ := maxinv_spec hI₁ htop
  have hle : maxinv (S.divI₁ a) ⪯ maxinv S.I := by
    rw [← hinv₁, S.divisorial_inv_eq hk ha 𝔪₁ hI₁𝔪₁]
    exact (maxinv_spec S.ne_bot S.ne_top).2 𝔪₁ (hII₁.trans hI₁𝔪₁)
  by_cases heq : maxinv (S.divI₁ a) = maxinv S.I
  swap
  · exact Or.inl ⟨hle, heq⟩
  obtain ⟨hfin, hprime, hcomax, hiff, -⟩ := theorem_3_3_3 S.ne_bot S.ne_top
  have h𝔭π := S.divisorial_𝔭_eq hk
  -- the other components do not contain `π`
  have hπP : ∀ P ∈ components S.I, P ≠ S.𝔭 → S.π ∉ P := by
    intro P hP hne hπ
    have := hcomax P hP S.𝔭 S.mem_components hne
    rw [sup_eq_left.2 (by rw [h𝔭π, Ideal.span_le, Set.singleton_subset_iff]; exact hπ)] at this
    exact (hprime P hP).1.ne_top this
  have hcomp : components (S.divI₁ a) = components S.I \ {S.𝔭} := by
    refine components_eq_of hI₁ htop (hfin.sdiff) (fun P hP => ⟨(hprime P hP.1).1, ?_⟩)
      (fun P hP Q hQ hne => hcomax P hP.1 Q hQ.1 hne) (fun 𝔪 _ h𝔪 => ?_)
    · -- `I₁ ⊆ P` for the other components `P`
      intro f hf
      have hπ := hπP P hP.1 hP.2
      have h1 : S.π ^ a * f ∈ P := (hprime P hP.1).2 (mem_divI.1 hf)
      rcases (hprime P hP.1).1.mem_or_mem h1 with h | h
      · exact absurd ((hprime P hP.1).1.mem_of_pow_mem a h) hπ
      · exact h
    · rw [S.divisorial_inv_eq hk ha 𝔪 h𝔪, heq, hiff 𝔪 (hII₁.trans h𝔪)]
      have hπ𝔪 := S.π_not_mem hk ha 𝔪 h𝔪
      constructor
      · rintro ⟨P, hP, hP𝔪⟩
        refine ⟨P, ⟨hP, fun h => hπ𝔪 ?_⟩, hP𝔪⟩
        rw [Set.mem_singleton_iff] at h
        exact hP𝔪 (h ▸ S.π_mem)
      · rintro ⟨P, hP, hP𝔪⟩
        exact ⟨P, hP.1, hP𝔪⟩
  refine Or.inr (Or.inr ⟨heq, hcomp, ?_⟩)
  unfold numComponents
  rw [hcomp]
  exact Set.ncard_sdiff_singleton_lt_of_mem S.mem_components hfin

end Divisorial

end PrincipalizationData

end BezoutCounterexample
