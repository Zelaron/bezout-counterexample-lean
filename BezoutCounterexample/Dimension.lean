import BezoutCounterexample.MainTheorem

/-!
# Proposition 6.2: Krull dimension

This file formalizes **Proposition 6.2** (`prop:dimension`) of the paper: there are prime ideals
`0 ⊊ 𝔭 ⊊ 𝔪` of `R` such that `𝔪` is maximal, `Δ ∈ 𝔭` and `1 + x ∈ 𝔪 \ 𝔭`. In particular `R` has
Krull dimension at least two and is not Noetherian.

The proof follows the paper. Put `f = 1 + x`.

* `powMulOneSub f` is the multiplicatively closed set `S = {fⁿ (1 - f r) : n ∈ ℕ, r ∈ R}`, closed
  under multiplication since `fⁿ(1 - f r) · fᵐ(1 - f t) = f^{n+m}(1 - f(r + t - f r t))`.
* `disjoint_span_Δ_powMulOneSub`: `S` does not meet `Δ R`. If `fⁿ (1 - f r) = Δ h`, put `g = f r`
  and `(w₁, w₂) = (g, 1 - g) M`; then `(w₁, w₂, Δ) = R` (checked at a maximal ideal `𝔫`), so
  `(g, 1 - g) M (u, v)ᵀ = 1 + Δ c` for some `u, v, c`, contrary to Lemma 5.3 with `μ = 1`.
* `exists_primes`: by Zorn's lemma there is an ideal `𝔭` maximal among the ideals containing `Δ`
  and disjoint from `S`; the standard maximal-disjointness argument
  (`Ideal.isPrime_of_maximally_disjoint`) shows that `𝔭` is prime. The ideal `𝔭 + f R` is proper,
  and a maximal ideal `𝔪 ⊇ 𝔭 + f R` does the job.
* `two_le_ringKrullDim`, `not_isNoetherianRing`: a Noetherian Bézout domain is a principal ideal
  domain, which has Krull dimension at most one.
* `dimension` collects the three statements of Proposition 6.2.

Remark 6.3 (`rem:dimension`: every Bézout domain that is not an elementary divisor domain has Krull
dimension at least two, by McGovern's theorem) is not formalized.
-/

noncomputable section

namespace BezoutCounterexample

open Matrix

/-- The multiplicatively closed set `S = {fⁿ (1 - f r) : n ∈ ℕ, r ∈ A}`: it contains `1`, and
`fⁿ(1 - f r) · fᵐ(1 - f t) = f^{n+m}(1 - f(r + t - f r t))`. -/
def powMulOneSub {A : Type*} [CommRing A] (f : A) : Submonoid A where
  carrier := {s | ∃ (n : ℕ) (r : A), s = f ^ n * (1 - f * r)}
  one_mem' := ⟨0, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨n, r, rfl⟩ ⟨m, t, rfl⟩
    exact ⟨n + m, r + t - f * r * t, by ring⟩

/-- `2` is a unit of `R`. -/
lemma R.isUnit_two : IsUnit (2 : R) := by
  have h := (isUnit_iff_ne_zero.2 (two_ne_zero : (2 : ℚ) ≠ 0)).map (algebraMap ℚ R)
  rwa [map_ofNat] at h

/-- **`S` does not meet `Δ R`**, where `S = {fⁿ (1 - f r)}` and `f = 1 + x`.

Suppose `fⁿ (1 - f r) = Δ h`. Put `g = f r` and `(w₁, w₂) = (g, 1 - g) M`. Then `(w₁, w₂, Δ) = R`:
otherwise a maximal ideal `𝔫` contains `w₁, w₂, Δ`. If `f ∈ 𝔫`, then `g ∈ 𝔫`, so
`(1 - g)(1 - x) = w₂ - y g ∈ 𝔫`, impossible as `1 - g ∉ 𝔫` and `f + (1 - x) = 2` is a unit.
Hence `f ∉ 𝔫`, so `1 - g ∈ 𝔫` (as `fⁿ (1 - g) = Δ h ∈ 𝔫`), so `g ∉ 𝔫`, and
`g (1 + x) = w₁ - y (1 - g) ∈ 𝔫` contradicts `1 + x = f ∉ 𝔫`. Thus `w₁ u + w₂ v = 1 + Δ c` for
some `u, v, c`, i.e. `(g, 1 - g) M (u, v)ᵀ = 1 + Δ c`, contrary to Lemma 5.3 with `μ = 1`. -/
theorem disjoint_span_Δ_powMulOneSub :
    Disjoint ((Ideal.span {R.ι Δ} : Ideal R) : Set R) (powMulOneSub (R.ι (1 + x))) := by
  rw [Set.disjoint_left]
  rintro s hs ⟨n, r, rfl⟩
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.1 hs
  set f := R.ι (1 + x) with hf
  have hfx : f = 1 + R.ι x := by rw [hf, map_add, map_one]
  set g := f * r with hg
  set w₁ := g * (1 + R.ι x) + (1 - g) * R.ι y with hw₁
  set w₂ := g * R.ι y + (1 - g) * (1 - R.ι x) with hw₂
  -- `(w₁, w₂) = (g, 1 - g) M`
  have hw : ∀ u v : R, ![g, 1 - g] ᵥ* (M.map R.ι) ⬝ᵥ ![u, v] = w₁ * u + w₂ * v := by
    intro u v
    rw [vecMul_M_dotProduct]
  -- the claim `(w₁, w₂, Δ) = R`
  have key : (Ideal.span {w₁, w₂, R.ι Δ} : Ideal R) = ⊤ := by
    by_contra hne
    obtain ⟨𝔫, h𝔫, hle⟩ := Ideal.exists_le_maximal _ hne
    have hprime := h𝔫.isPrime
    have hw₁𝔫 : w₁ ∈ 𝔫 := hle (Ideal.subset_span (by simp))
    have hw₂𝔫 : w₂ ∈ 𝔫 := hle (Ideal.subset_span (by simp))
    have hΔ𝔫 : R.ι Δ ∈ 𝔫 := hle (Ideal.subset_span (by simp))
    have hone : ∀ a : R, a ∈ 𝔫 → 1 - a ∈ 𝔫 → False := fun a ha ha' =>
      hprime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using 𝔫.add_mem ha ha'))
    -- `f ∉ 𝔫`
    have hf𝔫 : f ∉ 𝔫 := by
      intro hf𝔫
      have hg𝔫 : g ∈ 𝔫 := 𝔫.mul_mem_right _ hf𝔫
      have h₃ : (1 - g) * (1 - R.ι x) ∈ 𝔫 := by
        have e : (1 - g) * (1 - R.ι x) = w₂ - R.ι y * g := by rw [hw₂]; ring
        rw [e]
        exact 𝔫.sub_mem hw₂𝔫 (𝔫.mul_mem_left _ hg𝔫)
      rcases hprime.mem_or_mem h₃ with h₄ | h₄
      · -- `1 - g ∉ 𝔫` because `g ∈ 𝔫`
        exact hone g hg𝔫 h₄
      · -- `1 - x ∉ 𝔫` because `f + (1 - x) = 2` is a unit
        have h2 : (2 : R) ∈ 𝔫 := by
          have e : (2 : R) = f + (1 - R.ι x) := by rw [hfx]; ring
          rw [e]
          exact 𝔫.add_mem hf𝔫 h₄
        exact hprime.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 R.isUnit_two)
    -- hence `1 - g ∈ 𝔫`, since `fⁿ (1 - g) = Δ h ∈ 𝔫`
    have h1g : 1 - g ∈ 𝔫 := by
      have e : f ^ n * (1 - g) ∈ 𝔫 := by
        rw [← hh]
        exact 𝔫.mul_mem_left _ hΔ𝔫
      rcases hprime.mem_or_mem e with h₅ | h₅
      · exact absurd (hprime.mem_of_pow_mem _ h₅) hf𝔫
      · exact h₅
    -- then `g ∉ 𝔫`, and `g (1 + x) = w₁ - y (1 - g) ∈ 𝔫` contradicts `1 + x = f ∉ 𝔫`
    have h₆ : g * f ∈ 𝔫 := by
      have e : g * f = w₁ - R.ι y * (1 - g) := by rw [hw₁, hfx]; ring
      rw [e]
      exact 𝔫.sub_mem hw₁𝔫 (𝔫.mul_mem_left _ h1g)
    rcases hprime.mem_or_mem h₆ with h₇ | h₇
    · exact hone g h₇ h1g
    · exact hf𝔫 h₇
  -- hence `w₁ u + w₂ v = 1 + Δ c` for some `u, v, c`
  have h1 : (1 : R) ∈ (Ideal.span {w₁, w₂, R.ι Δ} : Ideal R) := by rw [key]; trivial
  obtain ⟨u, z, hz, hzu⟩ := Ideal.mem_span_insert.1 h1
  obtain ⟨v, c, hvc⟩ := Ideal.mem_span_pair.1 hz
  exact key_obstruction ⟨g, 1 - g, u, v, 1, -c, by
    rw [one_mul, hw]
    linear_combination -hzu + hvc⟩

/-- **Proposition 6.2** (`prop:dimension`), the chain of primes: there are prime ideals
`0 ⊊ 𝔭 ⊊ 𝔪` of `R` such that `𝔪` is maximal, `Δ ∈ 𝔭`, and `1 + x ∈ 𝔪 \ 𝔭`. -/
theorem exists_primes :
    ∃ 𝔭 𝔪 : Ideal R, 𝔭.IsPrime ∧ 𝔪.IsMaximal ∧ ⊥ < 𝔭 ∧ 𝔭 < 𝔪 ∧ R.ι Δ ∈ 𝔭 ∧
      R.ι (1 + x) ∈ 𝔪 ∧ R.ι (1 + x) ∉ 𝔭 := by
  set f := R.ι (1 + x)
  set S := powMulOneSub f
  -- Zorn's lemma: an ideal `𝔭` maximal among the ideals containing `Δ` and disjoint from `S`
  set 𝒮 : Set (Ideal R) := {I | Ideal.span {R.ι Δ} ≤ I ∧ Disjoint (I : Set R) S}
  have hchain : ∀ c ⊆ 𝒮, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ 𝒮, ∀ z ∈ c, z ≤ ub := by
    intro c hc hc' y hy
    have : Nonempty c := ⟨⟨y, hy⟩⟩
    refine ⟨sSup c, ⟨(hc hy).1.trans (le_sSup hy), Set.disjoint_left.2 fun a ha => ?_⟩,
      fun z hz => le_sSup hz⟩
    obtain ⟨p, hp⟩ := (Submodule.mem_iSup_of_directed _ hc'.directed).1 (sSup_eq_iSup' c ▸ ha)
    exact Set.disjoint_left.1 (hc p.2).2 hp
  obtain ⟨𝔭, -, h𝔭max⟩ :=
    zorn_le_nonempty₀ 𝒮 hchain (Ideal.span {R.ι Δ}) ⟨le_rfl, disjoint_span_Δ_powMulOneSub⟩
  have hΔ𝔭 : R.ι Δ ∈ 𝔭 := h𝔭max.1.1 (Ideal.mem_span_singleton_self _)
  have hdisj : Disjoint (𝔭 : Set R) S := h𝔭max.1.2
  -- the standard maximal-disjointness argument shows that `𝔭` is prime
  have h𝔭 : 𝔭.IsPrime := Ideal.isPrime_of_maximally_disjoint 𝔭 S hdisj
    fun J hJ hJS => h𝔭max.not_prop_of_gt hJ ⟨h𝔭max.1.1.trans hJ.le, hJS⟩
  -- since `f ∈ S`, `f ∉ 𝔭`
  have hf𝔭 : f ∉ 𝔭 := fun hf => Set.disjoint_left.1 hdisj hf ⟨1, 0, by simp⟩
  -- `𝔭 + f R` is proper: `1 = p + f r` would give `1 - f r ∈ 𝔭 ∩ S`
  have hne : 𝔭 ⊔ Ideal.span {f} ≠ ⊤ := by
    intro htop
    obtain ⟨p, hp, b, hb, hpb⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 htop)
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    have e : 1 - f * r = p := by rw [← hpb]; ring
    exact Set.disjoint_left.1 hdisj (e ▸ hp : 1 - f * r ∈ 𝔭) ⟨0, r, by ring⟩
  -- a maximal ideal `𝔪 ⊇ 𝔭 + f R`
  obtain ⟨𝔪, h𝔪, h𝔭𝔪⟩ := Ideal.exists_le_maximal _ hne
  have hf𝔪 : f ∈ 𝔪 := h𝔭𝔪 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  refine ⟨𝔭, 𝔪, h𝔭, h𝔪, ?_, lt_of_le_of_ne (le_sup_left.trans h𝔭𝔪) fun h => hf𝔭 (h ▸ hf𝔪),
    hΔ𝔭, hf𝔪, hf𝔭⟩
  -- `𝔭 ≠ 0` because `Δ ≠ 0`
  refine bot_lt_iff_ne_bot.2 fun h => R.Δ_ne_zero ?_
  rw [h] at hΔ𝔭
  exact hΔ𝔭

/-- **Proposition 6.2**: `R` has Krull dimension at least two. -/
theorem two_le_ringKrullDim : 2 ≤ ringKrullDim R := by
  obtain ⟨𝔭, 𝔪, h𝔭, h𝔪, h0, h1, -⟩ := exists_primes
  let p₀ : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  let p₁ : PrimeSpectrum R := ⟨𝔭, h𝔭⟩
  let p₂ : PrimeSpectrum R := ⟨𝔪, h𝔪.isPrime⟩
  have h₀₁ : p₀ < p₁ := h0
  have h₁₂ : p₁ < p₂ := h1
  let s : LTSeries (PrimeSpectrum R) :=
    ⟨2, ![p₀, p₁, p₂], fun i => by fin_cases i <;> simpa⟩
  exact_mod_cast Order.LTSeries.length_le_krullDim s

/-- A Noetherian Bézout domain is a principal ideal domain, and a principal ideal domain has Krull
dimension at most one. -/
theorem ringKrullDim_le_one_of_isNoetherianRing {D : Type*} [CommRing D] [IsDomain D]
    [IsBezout D] [hN : IsNoetherianRing D] : ringKrullDim D ≤ 1 := by
  have : IsPrincipalIdealRing D := ((IsBezout.TFAE (R := D)).out 1 2).1 hN
  exact Ring.krullDimLE_iff.1 inferInstance

/-- **Proposition 6.2**: `R` is not Noetherian. -/
theorem not_isNoetherianRing : ¬ IsNoetherianRing R := by
  intro h
  have h1 := ringKrullDim_le_one_of_isNoetherianRing (D := R)
  exact absurd (two_le_ringKrullDim.trans h1) (by decide)

/-- **Proposition 6.2** (`prop:dimension`). There are prime ideals `0 ⊊ 𝔭 ⊊ 𝔪` of `R` such that `𝔪`
is maximal, `Δ ∈ 𝔭`, and `1 + x ∈ 𝔪 \ 𝔭`. In particular, `R` has Krull dimension at least two and
is not Noetherian. -/
theorem dimension :
    (∃ 𝔭 𝔪 : Ideal R, 𝔭.IsPrime ∧ 𝔪.IsMaximal ∧ ⊥ < 𝔭 ∧ 𝔭 < 𝔪 ∧ R.ι Δ ∈ 𝔭 ∧
      R.ι (1 + x) ∈ 𝔪 ∧ R.ι (1 + x) ∉ 𝔭) ∧
    2 ≤ ringKrullDim R ∧ ¬ IsNoetherianRing R :=
  ⟨exists_primes, two_le_ringKrullDim, not_isNoetherianRing⟩

end BezoutCounterexample
