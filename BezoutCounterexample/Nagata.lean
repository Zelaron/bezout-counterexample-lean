import Mathlib

/-!
# Nagata's criterion for factoriality

Two facts about unique factorization domains, proved from Kaplansky's
criterion (`UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime`):

* `UniqueFactorizationMonoid.of_isLocalization`: a localization of a UFD is a UFD.
* `UniqueFactorizationMonoid.of_isLocalization_away` (Nagata's criterion): if `A` is a
  Noetherian domain, `p ∈ A` is a prime element and `A[1/p]` is a UFD, then `A` is a UFD.
-/

namespace BezoutCounterexample

open IsLocalization

section

variable {A : Type*} [CommRing A] [IsDomain A]

omit [IsDomain A] in
/-- The preimage of a prime ideal of a localization `L = A_S` is disjoint from `S`. -/
lemma disjoint_of_comap {S : Submonoid A} {L : Type*} [CommRing L] [Algebra A L]
    [IsLocalization S L] (Q : Ideal L) [hQ : Q.IsPrime] :
    Disjoint (S : Set A) (Q.comap (algebraMap A L) : Set A) := by
  rw [Set.disjoint_left]
  intro s hs hsQ
  exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hsQ (map_units L ⟨s, hs⟩))

/-- **A localization of a UFD is a UFD.** -/
theorem UniqueFactorizationMonoid.of_isLocalization [UniqueFactorizationMonoid A]
    (S : Submonoid A) (hS : (0 : A) ∉ S) (L : Type*) [CommRing L] [Algebra A L]
    [IsLocalization S L] : UniqueFactorizationMonoid L := by
  have hSle : S ≤ nonZeroDivisors A := fun s hs =>
    mem_nonZeroDivisors_of_ne_zero (fun h => hS (h ▸ hs))
  have : IsDomain L := isDomain_of_le_nonZeroDivisors L hSle
  rw [UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime]
  intro Q hQ0 hQ
  set P := Q.comap (algebraMap A L)
  have hP : P.IsPrime := Ideal.comap_isPrime _ Q
  have hdisj := disjoint_of_comap (S := S) Q
  have hP0 : P ≠ ⊥ := by
    intro h
    apply hQ0
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨⟨a, s⟩, rfl⟩ := mk'_surjective S q
    have ha : algebraMap A L a ∈ Q := by
      rw [← mk'_spec L a s]; exact Q.mul_mem_right _ hq
    have : a ∈ P := ha
    rw [h, Ideal.mem_bot] at this
    simp [this]
  obtain ⟨π, hπP, hπ⟩ :=
    (UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.1 inferInstance) P hP0 hP
  refine ⟨algebraMap A L π, hπP, ?_⟩
  have hspan : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
  have hdisj' : Disjoint (S : Set A) (Ideal.span {π} : Set A) :=
    hdisj.mono_right (by
      intro z hz
      exact (Ideal.span_le.2 (Set.singleton_subset_iff.2 hπP)) hz)
  have hmap := isPrime_of_isPrime_disjoint S L _ hspan hdisj'
  rw [Ideal.map_span, Set.image_singleton] at hmap
  have hne : algebraMap A L π ≠ 0 := fun h =>
    hπ.ne_zero ((IsLocalization.injective L hSle) (by rw [h, map_zero]))
  exact (Ideal.span_singleton_prime hne).1 hmap

/-- **Nagata's criterion.** Let `A` be a Noetherian domain and `p ∈ A` a prime element such that
`A[1/p]` is a UFD. Then `A` is a UFD. -/
theorem UniqueFactorizationMonoid.of_isLocalization_away [IsNoetherianRing A] {p : A}
    (hp : Prime p) (L : Type*) [CommRing L] [Algebra A L] [IsLocalization.Away p L]
    [UniqueFactorizationMonoid L] : UniqueFactorizationMonoid A := by
  have hSle : Submonoid.powers p ≤ nonZeroDivisors A := by
    rintro _ ⟨n, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hp.ne_zero)
  have : IsDomain L := isDomain_of_le_nonZeroDivisors L hSle
  have hinj : Function.Injective (algebraMap A L) := IsLocalization.injective L hSle
  rw [UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime]
  intro P hP0 hP
  by_cases hpP : p ∈ P
  · exact ⟨p, hpP, hp⟩
  -- `P` is disjoint from the powers of `p`
  have hdisj : Disjoint (Submonoid.powers p : Set A) (P : Set A) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ h
    exact hpP (hP.mem_of_pow_mem n h)
  set Q := P.map (algebraMap A L)
  have hQ : Q.IsPrime := isPrime_of_isPrime_disjoint _ L P hP hdisj
  have hQP : Q.comap (algebraMap A L) = P := under_map_of_isPrime_disjoint _ L hP hdisj
  have hQ0 : Q ≠ ⊥ := by
    intro h
    apply hP0
    rw [eq_bot_iff]
    intro a ha
    have : algebraMap A L a ∈ Q := Ideal.mem_map_of_mem _ ha
    rw [h, Ideal.mem_bot] at this
    rw [Ideal.mem_bot]
    exact hinj (by rw [this, map_zero])
  obtain ⟨q, hqQ, hq⟩ :=
    (UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.1 inferInstance) Q hQ0 hQ
  obtain ⟨⟨a, s⟩, hqa⟩ := mk'_surjective (Submonoid.powers p) q
  simp only at hqa
  -- `a/1 = q · s` is associated to `q`
  have has : algebraMap A L a = q * algebraMap A L s := by rw [← hqa, mk'_spec]
  have haP : a ∈ P := by
    rw [← hQP]
    show algebraMap A L a ∈ Q
    rw [has]; exact Q.mul_mem_right _ hqQ
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, mul_eq_zero] at has
    rcases has with h | h
    · exact hq.ne_zero h
    · exact (map_units L s).ne_zero h
  -- remove the factors of `p`
  obtain ⟨a', ha', hpa'⟩ :=
    (FiniteMultiplicity.of_not_isUnit hp.not_isUnit ha0).exists_eq_pow_mul_and_not_dvd
  set m := multiplicity p a
  have ha'P : a' ∈ P := by
    rw [ha'] at haP
    rcases hP.mem_or_mem haP with h | h
    · exact absurd (hP.mem_of_pow_mem m h) hpP
    · exact h
  refine ⟨a', ha'P, ?_⟩
  -- `a'/1` is associated to the prime `q`
  have hassoc : Associated q (algebraMap A L a') := by
    have h1 : Associated q (algebraMap A L a) := by
      rw [has]; exact associated_mul_unit_right q _ (map_units L s)
    have h2 : Associated (algebraMap A L a') (algebraMap A L a) := by
      rw [ha', map_mul]
      exact associated_unit_mul_right _ _ ((IsLocalization.Away.algebraMap_isUnit p).pow m |>
        fun h => by simpa [map_pow] using h)
    exact h1.trans h2.symm
  have ha'L : Prime (algebraMap A L a') := hassoc.prime hq
  refine ⟨fun h => hpa' (h ▸ dvd_zero p), fun hu => ha'L.not_isUnit (hu.map _), ?_⟩
  intro b c hbc
  have hbcL : algebraMap A L a' ∣ algebraMap A L b * algebraMap A L c := by
    rw [← map_mul]; exact map_dvd _ hbc
  -- if `a'/1 ∣ b/1` then `a' ∣ b`
  have key : ∀ d : A, algebraMap A L a' ∣ algebraMap A L d → a' ∣ d := by
    intro d ⟨e, he⟩
    obtain ⟨⟨f, ⟨_, n, rfl⟩⟩, rfl⟩ := mk'_surjective (Submonoid.powers p) e
    simp only at he
    have h1 : algebraMap A L (d * p ^ n) = algebraMap A L (a' * f) := by
      rw [map_mul, he, map_mul, mul_assoc, mk'_spec]
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers p) L).1 h1
    simp only at hk
    -- `p ^ (k + n) * d = a' * (p ^ k * f)`
    have h2 : p ^ (k + n) ∣ a' * (p ^ k * f) := ⟨d, by rw [pow_add]; linear_combination hk.symm⟩
    obtain ⟨g, hg⟩ := hp.pow_dvd_of_dvd_mul_left (k + n) hpa' h2
    refine ⟨g, ?_⟩
    have h3 : p ^ (k + n) * d = p ^ (k + n) * (a' * g) := by
      rw [pow_add] at hg ⊢
      linear_combination hk + a' * hg
    exact mul_left_cancel₀ (pow_ne_zero _ hp.ne_zero) h3
  rcases ha'L.dvd_or_dvd hbcL with h | h
  · exact Or.inl (key b h)
  · exact Or.inr (key c h)

end

end BezoutCounterexample
