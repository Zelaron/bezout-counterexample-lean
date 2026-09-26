import BezoutCounterexample.Abstract

/-!
# Krull dimension and Noetherianity of `R`

Proposition 6.2 (`prop:dimension`) of the paper.

The ring `R` of Construction 5.1 has Krull dimension at least two and is not Noetherian.

* `exists_prime_le_maximal`, `two_le_ringKrullDim_of_forall_ne`: if no `fⁿ (1 - f r)` is a
  multiple of a nonzero element `d` of a domain, there is a chain of primes `0 ⊊ 𝔭 ⊊ 𝔪` with
  `d ∈ 𝔭` and `f ∈ 𝔪 \ 𝔭`.
* `exists_unit_value_mod_of_pow_mul`: if `(1 + x)ⁿ (1 - (1 + x) r) ∈ (Δ)`, then, with
  `g = (1 + x) r`, the row `(g, 1 - g) M` is unimodular modulo `Δ`.
* `R.pow_mul_one_sub_ne`: by the key obstruction `R.no_unit_value_mod` (Lemma 5.3), no
  `(1 + x)ⁿ (1 - (1 + x) r)` is a multiple of `Δ` in `R`.
* `R.exists_prime_lt_maximal`, `R.two_le_ringKrullDim`, `R.not_isNoetherianRing`
  (Proposition 6.2), and `proposition_6_2` for the ring of Theorem 1.1.
* `LocallyMobius.two_le_ringKrullDim`, `LocallyMobius.not_isNoetherianRing`,
  `IsMobiusTower.two_le_ringKrullDim`: the same for every locally Möbius domain, in particular for
  the direct limit of any Möbius tower, i.e. for every run of Construction 5.1.
-/

noncomputable section

namespace BezoutCounterexample

/-- The multiplicative set `{fⁿ (1 - f r) : n ∈ ℕ, r ∈ A}`. -/
def powMulOneSub {A : Type*} [CommRing A] (f : A) : Submonoid A where
  carrier := {s | ∃ (n : ℕ) (r : A), s = f ^ n * (1 - f * r)}
  one_mem' := ⟨0, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨n, r, rfl⟩ ⟨m, t, rfl⟩
    exact ⟨n + m, r + t - f * r * t, by ring⟩

/-- If no `fⁿ (1 - f r)` is a multiple of `d`, then there are prime ideals `𝔭 ⊆ 𝔪` with `𝔪`
maximal, `d ∈ 𝔭` and `f ∈ 𝔪 \ 𝔭`. -/
theorem exists_prime_le_maximal {A : Type*} [CommRing A] (d f : A)
    (h : ∀ (n : ℕ) (r c : A), f ^ n * (1 - f * r) ≠ d * c) :
    ∃ P m : Ideal A, P.IsPrime ∧ m.IsMaximal ∧ P ≤ m ∧ d ∈ P ∧ f ∉ P ∧ f ∈ m := by
  have hdisj : Disjoint ((Ideal.span {d} : Ideal A) : Set A) (powMulOneSub f) := by
    rw [Set.disjoint_left]
    rintro s hs ⟨n, r, rfl⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hs
    exact h n r c (by rw [← hc, mul_comm])
  obtain ⟨P, hP, hle, hPS⟩ := Ideal.exists_le_prime_disjoint _ _ hdisj
  have hfP : f ∉ P := fun hf => Set.disjoint_left.1 hPS hf ⟨1, 0, by simp⟩
  have hne : P ⊔ Ideal.span {f} ≠ ⊤ := by
    intro htop
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 htop)
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    have h1 : 1 - f * r = a := by rw [← hab]; ring
    exact Set.disjoint_left.1 hPS (h1 ▸ ha : 1 - f * r ∈ P) ⟨0, r, by ring⟩
  obtain ⟨m, hm, hPm⟩ := Ideal.exists_le_maximal _ hne
  exact ⟨P, m, hP, hm, le_sup_left.trans hPm, hle (Ideal.mem_span_singleton_self d), hfP,
    hPm (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))⟩

/-- If `d` is a nonzero element of a domain `A` such that no `fⁿ (1 - f r)` is a multiple of `d`,
then `A` has Krull dimension at least two: the primes of `exists_prime_le_maximal` give a chain
`0 ⊊ 𝔭 ⊊ 𝔪`. -/
theorem two_le_ringKrullDim_of_forall_ne {A : Type*} [CommRing A] [IsDomain A] {d : A}
    (hd : d ≠ 0) (f : A) (h : ∀ (n : ℕ) (r c : A), f ^ n * (1 - f * r) ≠ d * c) :
    2 ≤ ringKrullDim A := by
  obtain ⟨P, m, hP, hm, hPm, hdP, hfP, hfm⟩ := exists_prime_le_maximal d f h
  let p₀ : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
  let p₁ : PrimeSpectrum A := ⟨P, hP⟩
  let p₂ : PrimeSpectrum A := ⟨m, hm.isPrime⟩
  have h₀₁ : p₀ < p₁ := by
    refine lt_of_le_of_ne bot_le fun he => hd ?_
    have : d ∈ (⊥ : Ideal A) := by
      have := congrArg PrimeSpectrum.asIdeal he
      simp only [p₀, p₁] at this
      rw [this]; exact hdP
    simpa using this
  have h₁₂ : p₁ < p₂ := lt_of_le_of_ne hPm fun he => hfP (by
    have := congrArg PrimeSpectrum.asIdeal he
    simp only [p₁, p₂] at this
    rw [this]; exact hfm)
  let s : LTSeries (PrimeSpectrum A) :=
    ⟨2, ![p₀, p₁, p₂], fun i => by fin_cases i <;> simpa⟩
  exact_mod_cast Order.LTSeries.length_le_krullDim s

/-- Let `2` be a unit of `B`, and suppose that `(1 + X)ⁿ (1 - (1 + X) r)` is a multiple of `D`.
With `g = (1 + X) r`, the row `(g, 1 - g) M`, where `M = [[1 + X, Y], [Y, 1 - X]]`, is unimodular
modulo `D`. -/
theorem exists_unit_value_mod_of_pow_mul {B : Type*} [CommRing B] (two : IsUnit (2 : B))
    (X Y D r h : B) (n : ℕ) (hrel : (1 + X) ^ n * (1 - (1 + X) * r) = D * h) :
    ∃ u v c : B, ((1 + X) * r * (1 + X) + (1 - (1 + X) * r) * Y) * u +
      ((1 + X) * r * Y + (1 - (1 + X) * r) * (1 - X)) * v = 1 + D * c := by
  set g := (1 + X) * r with hg
  have key : Ideal.span {g * (1 + X) + (1 - g) * Y, g * Y + (1 - g) * (1 - X), D} = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    have hPp := hP.isPrime
    have h₁ : g * (1 + X) + (1 - g) * Y ∈ P := hle (Ideal.subset_span (by simp))
    have h₂ : g * Y + (1 - g) * (1 - X) ∈ P := hle (Ideal.subset_span (by simp))
    have hD : D ∈ P := hle (Ideal.subset_span (by simp))
    have hone : ∀ a : B, a ∈ P → 1 - a ∈ P → False := fun a ha ha' =>
      hPp.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using P.add_mem ha ha'))
    -- `1 + X ∉ P`: otherwise `g ∈ P`, hence `1 - X ∈ P`, and `2 ∈ P`
    have hf : 1 + X ∉ P := by
      intro hf
      have hg' : g ∈ P := by rw [hg]; exact P.mul_mem_right _ hf
      have h₃ : (1 - g) * (1 - X) ∈ P := by
        have : (1 - g) * (1 - X) = (g * Y + (1 - g) * (1 - X)) - Y * g := by ring
        rw [this]; exact P.sub_mem h₂ (P.mul_mem_left Y hg')
      rcases hPp.mem_or_mem h₃ with h₄ | h₄
      · exact hone g hg' h₄
      · have h2P : (2 : B) ∈ P := by
          have : (2 : B) = (1 + X) + (1 - X) := by ring
          rw [this]; exact P.add_mem hf h₄
        exact hPp.ne_top (Ideal.eq_top_of_isUnit_mem _ h2P two)
    -- hence `1 - g ∈ P`, so `g (1 + X) ∈ P`, which is impossible
    have hfe : (1 + X) ^ n * (1 - g) ∈ P := by rw [hrel]; exact P.mul_mem_right _ hD
    rcases hPp.mem_or_mem hfe with h₃ | h₃
    · exact hf (hPp.mem_of_pow_mem _ h₃)
    · have h₄ : g * (1 + X) ∈ P := by
        have : g * (1 + X) = (g * (1 + X) + (1 - g) * Y) - Y * (1 - g) := by ring
        rw [this]; exact P.sub_mem h₁ (P.mul_mem_left Y h₃)
      rcases hPp.mem_or_mem h₄ with h₅ | h₅
      · exact hone g h₅ h₃
      · exact hf h₅
  have h1 : (1 : B) ∈ Ideal.span {g * (1 + X) + (1 - g) * Y, g * Y + (1 - g) * (1 - X), D} := by
    rw [key]; trivial
  obtain ⟨a, z, hz, hza⟩ := Ideal.mem_span_insert.1 h1
  obtain ⟨b, c, hbc⟩ := Ideal.mem_span_pair.1 hz
  refine ⟨a, b, -c, ?_⟩
  linear_combination -hza + hbc

/-- `2` is a unit in every ring receiving `A₀ = ℚ[x,y]`. -/
lemma isUnit_two_of_A₀ {D : Type*} [CommRing D] (ι : A₀ →+* D) : IsUnit (2 : D) := by
  refine IsUnit.of_mul_eq_one (ι (MvPolynomial.C (1 / 2))) ?_
  have : (2 : D) = ι (MvPolynomial.C 2) := by rw [map_ofNat MvPolynomial.C 2, map_ofNat]
  rw [this, ← map_mul, ← map_mul]
  norm_num

/-- A Bézout domain of Krull dimension at least two is not Noetherian: a Noetherian Bézout domain
is a principal ideal domain, and principal ideal domains have Krull dimension at most one. -/
theorem not_isNoetherianRing_of_two_le {D : Type*} [CommRing D] [IsDomain D] [IsBezout D]
    (h : 2 ≤ ringKrullDim D) : ¬ IsNoetherianRing D := by
  intro hN
  have : IsPrincipalIdealRing D := ((IsBezout.TFAE (R := D)).out 1 2).1 hN
  have h1 : ringKrullDim D ≤ 1 := Ring.krullDimLE_iff.1 inferInstance
  exact absurd (h.trans h1) (by decide)

namespace R

variable (hPE : CoprimePairPE)

/-- In `R`, no element `(1 + x)ⁿ (1 - (1 + x) r)` is a multiple of `Δ`: otherwise
`exists_unit_value_mod_of_pow_mul` would contradict the key obstruction `no_unit_value_mod`. -/
theorem pow_mul_one_sub_ne (n : ℕ) (r c : R hPE) :
    (1 + ι hPE x) ^ n * (1 - (1 + ι hPE x) * r) ≠ ι hPE Δ * c := by
  intro hrel
  obtain ⟨u, v, c', h⟩ :=
    exists_unit_value_mod_of_pow_mul (isUnit_two_of_A₀ (ι hPE)) (ι hPE x) (ι hPE y) (ι hPE Δ) r c n
      hrel
  apply no_unit_value_mod hPE ((1 + ι hPE x) * r) (1 - (1 + ι hPE x) * r) u v 1 c'
  linear_combination h

/-- **Proposition 6.2**: there are prime ideals `0 ⊊ 𝔭 ⊊ 𝔪` of `R`, with `𝔪` maximal,
`Δ ∈ 𝔭` and `1 + x ∈ 𝔪 \ 𝔭`. -/
theorem exists_prime_lt_maximal :
    ∃ P m : Ideal (R hPE), P.IsPrime ∧ m.IsMaximal ∧ ⊥ < P ∧ P < m ∧ ι hPE Δ ∈ P ∧
      1 + ι hPE x ∉ P ∧ 1 + ι hPE x ∈ m := by
  obtain ⟨P, m, hP, hm, hPm, hdP, hfP, hfm⟩ :=
    exists_prime_le_maximal (ι hPE Δ) (1 + ι hPE x) (pow_mul_one_sub_ne hPE)
  refine ⟨P, m, hP, hm, bot_lt_iff_ne_bot.2 fun h => R.Δ_ne_zero hPE ?_,
    lt_of_le_of_ne hPm fun h => hfP (h ▸ hfm), hdP, hfP, hfm⟩
  simpa [h] using hdP

/-- **Proposition 6.2**: `R` has Krull dimension at least two. -/
theorem two_le_ringKrullDim : 2 ≤ ringKrullDim (R hPE) :=
  two_le_ringKrullDim_of_forall_ne (R.Δ_ne_zero hPE) _ (pow_mul_one_sub_ne hPE)

/-- **Proposition 6.2**: `R` is not Noetherian (a Noetherian Bézout domain is a principal
ideal domain, and principal ideal domains have Krull dimension at most one). -/
theorem not_isNoetherianRing : ¬ IsNoetherianRing (R hPE) :=
  not_isNoetherianRing_of_two_le (two_le_ringKrullDim hPE)

end R

namespace LocallyMobius

variable {D : Type} [CommRing D] {ι : A₀ →+* D}

/-- In a locally Möbius ring, no `(1 + x)ⁿ (1 - (1 + x) r)` is a multiple of `Δ`. -/
theorem pow_mul_one_sub_ne (h : LocallyMobius D ι) (n : ℕ) (r c : D) :
    (1 + ι x) ^ n * (1 - (1 + ι x) * r) ≠ ι Δ * c := by
  intro hrel
  obtain ⟨u, v, c', h'⟩ :=
    exists_unit_value_mod_of_pow_mul (isUnit_two_of_A₀ ι) (ι x) (ι y) (ι Δ) r c n hrel
  apply h.no_unit_value_mod ((1 + ι x) * r) (1 - (1 + ι x) * r) u v 1 c'
  linear_combination h'

/-- **Abstract Proposition 6.2**: a locally Möbius domain in which `Δ ≠ 0` has Krull dimension at
least two. -/
theorem two_le_ringKrullDim [IsDomain D] (h : LocallyMobius D ι) (hΔ : ι Δ ≠ 0) :
    2 ≤ ringKrullDim D :=
  two_le_ringKrullDim_of_forall_ne hΔ _ h.pow_mul_one_sub_ne

/-- **Abstract Proposition 6.2**: a locally Möbius Bézout domain in which `Δ ≠ 0` is not
Noetherian. -/
theorem not_isNoetherianRing [IsDomain D] [IsBezout D] (h : LocallyMobius D ι) (hΔ : ι Δ ≠ 0) :
    ¬ IsNoetherianRing D :=
  not_isNoetherianRing_of_two_le (h.two_le_ringKrullDim hΔ)

end LocallyMobius

/-- **Proposition 6.2 for any Möbius tower** (in particular for every run of Construction 5.1,
by `isMobiusTower_of_sequence`): the direct limit has Krull dimension at least two and is not
Noetherian. -/
theorem IsMobiusTower.two_le_ringKrullDim {I : Type} [Preorder I] [IsDirectedOrder I]
    {G : I → Type} [∀ i, CommRing (G i)] {f : ∀ i j, i ≤ j → G i →+* G j}
    [DirectedSystem G fun i j h => f i j h] [∀ i, IsDomain (G i)] {i₀ : I} {ι : A₀ →+* G i₀}
    (hT : IsMobiusTower G f i₀ ι) :
    2 ≤ ringKrullDim (Lim G f) ∧ ¬ IsNoetherianRing (Lim G f) := by
  have := hT.isDomain
  have := hT.isBezout
  exact ⟨hT.locallyMobius.two_le_ringKrullDim hT.Δ_ne_zero,
    hT.locallyMobius.not_isNoetherianRing hT.Δ_ne_zero⟩

/-- **Proposition 6.2**, for the ring of Theorem 1.1 (`Principalization.principalizationExtension`
being proved). -/
theorem proposition_6_2 :
    (∃ P m : Ideal (R coprimePairPE_holds), P.IsPrime ∧ m.IsMaximal ∧ ⊥ < P ∧ P < m ∧
      R.ι coprimePairPE_holds Δ ∈ P ∧ 1 + R.ι coprimePairPE_holds x ∉ P ∧
      1 + R.ι coprimePairPE_holds x ∈ m) ∧
    2 ≤ ringKrullDim (R coprimePairPE_holds) ∧ ¬ IsNoetherianRing (R coprimePairPE_holds) :=
  ⟨R.exists_prime_lt_maximal _, R.two_le_ringKrullDim _, R.not_isNoetherianRing _⟩

end BezoutCounterexample
