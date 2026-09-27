import BezoutCounterexample.LengthControl

/-!
# Section 4.4: real points of the torsor (Lemma 4.5)

In the torsor step, let `K ⊂ Spec(A)(ℝ)` be compact, put `Eᵢ = 2 d!/jᵢ` (an even integer), and let
`K' ⊂ Spec(U)(ℝ)` be the set of real points `z'` with
`z'|_A ∈ K`, `z'(s) ≥ 0`, `∑ z'(hᵢ)^{Eᵢ} = 1`, and `z'(σᵢ) = z'(hᵢ)^{Eᵢ - 1}`
(`PrincipalizationData.sphereBundle`).

**Lemma 4.5** (`lem:sphere-bundle`): `K'` is compact and `K' → K` is a monotone surjection; the
fibre over `z ∈ K` is a single point if `𝔭 ⊄ ker z`, and a continuous image of `ℝᵏ ∖ {0}` if
`𝔭 ⊆ ker z` (`sphere_bundle`). Equation (4.1): `z'(s)^{2 d!} = ∑ z(gᵢ)^{Eᵢ} =: ν(z)` (`s_norm`).

For `k = 1` the same construction would produce two-point fibres over `V(𝔭)(ℝ)`, since
`ℝ ∖ {0}` is disconnected; this is why divisorial centers are divided out rather than blown up.
-/

noncomputable section

namespace BezoutCounterexample

open IsLocalRing Principalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [UniqueFactorizationMonoid A]

namespace PrincipalizationData

variable (S : PrincipalizationData A)

/-- The exponents `Eᵢ = 2 d!/jᵢ`. -/
def E (i : Fin (S.ℓ + 1)) : ℕ := 2 * (S.d.factorial / S.jdeg i)

/-- `Eᵢ` is an even integer with `jᵢ Eᵢ = 2 d!`. -/
theorem E_spec (i : Fin (S.ℓ + 1)) : Even (S.E i) ∧ S.jdeg i * S.E i = 2 * S.d.factorial :=
  ⟨even_two_mul _, gdeg_mul_sphE S.ne_bot S.hmax S.h𝔭 S.d_pos i⟩

/-- The set `K' ⊂ Spec(U)(ℝ)` of Lemma 4.5 (a weighted sphere bundle over `K`). -/
def sphereBundle (K : Set (RealPt A)) : Set (RealPt S.U) :=
  {z' | RealPt.comap (algebraMap A S.U) z' ∈ K ∧ 0 ≤ z' S.sU ∧
    ∑ i, z' (algebraMap S.𝓡 S.U (S.h i)) ^ S.E i = 1 ∧
    ∀ i, z' (Jou.σ S.h i) = z' (algebraMap S.𝓡 S.U (S.h i)) ^ (S.E i - 1)}

/-- `K'` is the engine's weighted sphere bundle `torsorK`. -/
theorem sphereBundle_eq (K : Set (RealPt A)) :
    S.sphereBundle K = torsorK S.ne_bot S.hmax S.h𝔭 S.π_mem_fil K := rfl

/-- `ν(z) = ∑ z(gᵢ)^{Eᵢ}`. -/
def ν (z : RealPt A) : ℝ := ∑ i, z (S.g i) ^ S.E i

/-- (4.1): every `z' ∈ K'` satisfies `z'(s)^{2 d!} = ν(z'|_A)`. -/
theorem s_norm {K : Set (RealPt A)} {z' : RealPt S.U} (hz' : z' ∈ S.sphereBundle K) :
    z' S.sU ^ (2 * S.d.factorial) = S.ν (RealPt.comap (algebraMap A S.U) z') :=
  s_pow_eq S.ne_bot S.hmax S.h𝔭 S.d_pos S.π_mem_fil z' hz'.2.2.1

/-- `ν(z) > 0` if and only if `𝔭 ⊄ ker z`. -/
theorem ν_pos_iff (z : RealPt A) : 0 < S.ν z ↔ ¬ S.𝔭 ≤ RingHom.ker z := by
  have hnn : 0 ≤ S.ν z := gNorm_nonneg S.ne_bot S.hmax S.h𝔭 z
  constructor
  · intro hpos hle
    apply hpos.ne'
    refine Finset.sum_eq_zero fun i _ => ?_
    have hg : z (S.g i) = 0 :=
      hle (genCoeff_mem_p S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw S.π_mem_fil i)
    rw [hg]
    exact zero_pow (Nat.pos_iff_ne_zero.1 (sphE_pos S.ne_bot S.hmax S.h𝔭 S.d_pos i))
  · intro hle
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exact absurd (fun g hg => kills_of_gNorm_zero S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw
        h.symm g hg) hle

/-- **Lemma 4.5** (`lem:sphere-bundle`). In the torsor step (`k ≥ 2`), `K'` is compact and
`K' → K` is a monotone surjection. The fibre over `z ∈ K` is a single point if `𝔭 ⊄ ker z`, and a
continuous image of `ℝᵏ ∖ {0}` if `𝔭 ⊆ ker z`. -/
theorem sphere_bundle (hk : 2 ≤ S.k) {K : Set (RealPt A)} (hK : IsCompact K) :
    IsCompact (S.sphereBundle K) ∧
    IsMonotoneSurjOn (RealPt.comap (algebraMap A S.U)) (S.sphereBundle K) K ∧
    (∀ z ∈ K, ¬ S.𝔭 ≤ RingHom.ker z →
      ∃! z' : RealPt S.U, z' ∈ S.sphereBundle K ∧ RealPt.comap (algebraMap A S.U) z' = z) ∧
    (∀ z ∈ K, S.𝔭 ≤ RingHom.ker z →
      ∃ Γ : {a : Fin S.k → ℝ // a ≠ 0} → RealPt S.U, Continuous Γ ∧
        Set.range Γ = {z' | z' ∈ S.sphereBundle K ∧ RealPt.comap (algebraMap A S.U) z' = z}) := by
  have hk2 : maxinv S.I 1 ≠ 0 := (S.e_ne_zero_iff 1).2 (by omega)
  refine ⟨torsorK_isCompact S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw S.π_mem_fil hK, ?_, ?_, ?_⟩
  · -- `K' → K` is a monotone surjection (as in the engine's `torsorK_monotone`)
    have hmaps : Set.MapsTo (RealPt.comap (algebraMap A S.U)) (S.sphereBundle K) K :=
      fun w hw => hw.1
    refine ⟨hmaps, ⟨?_, ?_, ?_⟩⟩
    · exact ((RealPt.continuous_comap _).comp continuous_subtype_val).subtype_mk _
    · rintro ⟨z, hzK⟩
      rcases (gNorm_nonneg S.ne_bot S.hmax S.h𝔭 (d := S.d) (π := S.π) z).lt_or_eq with hpos | h0
      · exact ⟨⟨ptA S.ne_bot S.hmax S.h𝔭 S.d_pos S.π_mem_fil z hpos,
          ptA_mem S.ne_bot S.hmax S.h𝔭 S.d_pos S.π_mem_fil K hzK hpos⟩,
          Subtype.ext (ptA_comap S.ne_bot S.hmax S.h𝔭 S.d_pos S.π_mem_fil z hpos)⟩
      · have hz := kills_of_gNorm_zero S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw h0.symm
        obtain ⟨P⟩ := LocPres.nonempty S.ne_bot S.hmax S.h𝔭 S.hw z hz
        have hk : 0 < P.k := by have := P.hk2 hk2; omega
        set u : ({0}ᶜ : Set (Fin P.k → ℝ)) := ⟨fun _ => 1, fun h => by
          have := congrFun h ⟨0, hk⟩; simp at this⟩
        exact ⟨⟨P.Gamma S.ne_bot S.hmax S.h𝔭 S.d_pos hz S.π_mem_fil u,
          P.Gamma_mem S.ne_bot S.hmax S.h𝔭 S.d_pos hz S.π_mem_fil hzK u⟩,
          Subtype.ext (P.Gamma_comap S.ne_bot S.hmax S.h𝔭 S.d_pos hz S.π_mem_fil u)⟩
    · rintro ⟨z, hzK⟩
      apply isConnected_restrict_fiber
      show IsConnected (torsorFib S.ne_bot S.hmax S.h𝔭 S.π_mem_fil K z)
      rcases (gNorm_nonneg S.ne_bot S.hmax S.h𝔭 (d := S.d) (π := S.π) z).lt_or_eq with hpos | h0
      · have : torsorFib S.ne_bot S.hmax S.h𝔭 S.π_mem_fil K z =
            {ptA S.ne_bot S.hmax S.h𝔭 S.d_pos S.π_mem_fil z hpos} := by
          ext w
          constructor
          · rintro ⟨hwK, hwz⟩
            exact eq_ptA S.ne_bot S.hmax S.h𝔭 S.d_pos S.π_mem_fil K hwK hwz hpos
          · rintro rfl
            exact ⟨ptA_mem S.ne_bot S.hmax S.h𝔭 S.d_pos S.π_mem_fil K hzK hpos,
              ptA_comap S.ne_bot S.hmax S.h𝔭 S.d_pos S.π_mem_fil z hpos⟩
        rw [this]
        exact isConnected_singleton
      · exact fib_connected S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw S.π_mem_fil
          (kills_of_gNorm_zero S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw h0.symm) hk2 hzK
  · -- over `z` with `𝔭 ⊄ ker z` the fibre is a single point
    intro z hzK hz
    have hpos : 0 < S.ν z := (S.ν_pos_iff z).2 hz
    refine ⟨ptA S.ne_bot S.hmax S.h𝔭 S.d_pos S.π_mem_fil z hpos,
      ⟨ptA_mem S.ne_bot S.hmax S.h𝔭 S.d_pos S.π_mem_fil K hzK hpos,
        ptA_comap S.ne_bot S.hmax S.h𝔭 S.d_pos S.π_mem_fil z hpos⟩, ?_⟩
    rintro w ⟨hwK, hwz⟩
    exact eq_ptA S.ne_bot S.hmax S.h𝔭 S.d_pos S.π_mem_fil K hwK hwz hpos
  · -- over `z` with `𝔭 ⊆ ker z` the fibre is the image of `ℝᵏ ∖ {0}` under `Γ`
    intro z hzK hle
    have hz : ∀ g ∈ S.𝔭, z g = 0 := fun g hg => hle hg
    obtain ⟨P⟩ := LocPres.nonempty S.ne_bot S.hmax S.h𝔭 S.hw z hz
    -- the local number of nonzero weights is `k`
    have hPk : P.k = S.k := by
      have hsupp : ∀ i : Fin P.n, S.e i ≠ 0 ↔ (i : ℕ) < P.k := fun i => by
        rw [show S.e i = P.e i from (P.hev i).symm]; exact P.hsupp i
      -- `maxinv(I)` vanishes from index `dim A = P.n` on
      have hvan : ∀ i, P.n ≤ i → S.e i = 0 := by
        obtain ⟨⟨𝔪, h𝔪, hI𝔪, hinv⟩, -⟩ := maxinv_spec S.ne_bot S.ne_top
        obtain ⟨n', e', he', hext⟩ := invAt_inv S.ne_bot hI𝔪
        obtain ⟨J, -, -⟩ := he'.1
        have hn' : n' = P.n := by
          have h1 := chart_size_eq_ringKrullDim J.c
          have h2 := chart_size_eq_ringKrullDim P.c
          rw [h1] at h2; exact_mod_cast h2
        intro i hi
        show maxinv S.I i = 0
        rw [← hinv, ← hext]
        simp [ext0, show ¬ i < n' by omega]
      have hkn := P.hkn
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · -- `P.k < k`: the weight at index `P.k` is nonzero
        have h1 := (S.e_ne_zero_iff P.k).2 h
        by_cases hPn : P.k < P.n
        · exact absurd ((hsupp ⟨P.k, hPn⟩).1 h1) (lt_irrefl _)
        · exact h1 (hvan P.k (by omega))
      · -- `k < P.k ≤ P.n`: the weight at index `k` is nonzero
        have h1 := (hsupp ⟨S.k, by omega⟩).2 h
        exact absurd ((S.e_ne_zero_iff S.k).1 h1) (lt_irrefl _)
    -- reindex `ℝᵏ ∖ {0}` along `P.k = k`
    let φ : {a : Fin S.k → ℝ // a ≠ 0} → ({0}ᶜ : Set (Fin P.k → ℝ)) := fun a =>
      ⟨a.1 ∘ Fin.cast hPk, fun h => a.2 (funext fun i => by
        have := congrFun h (Fin.cast hPk.symm i)
        simpa using this)⟩
    have hφ : Function.Surjective φ := fun u =>
      ⟨⟨u.1 ∘ Fin.cast hPk.symm, fun h => u.2 (funext fun i => by
        have := congrFun h (Fin.cast hPk i)
        simpa using this)⟩, Subtype.ext (funext fun i => by simp [φ])⟩
    have hφc : Continuous φ := by
      apply Continuous.subtype_mk
      exact continuous_pi fun i => (continuous_apply (Fin.cast hPk i)).comp continuous_subtype_val
    refine ⟨P.Gamma S.ne_bot S.hmax S.h𝔭 S.d_pos hz S.π_mem_fil ∘ φ,
      (P.continuous_Gamma S.ne_bot S.hmax S.h𝔭 S.d_pos hz S.π_mem_fil).comp hφc, ?_⟩
    rw [hφ.range_comp]
    exact (P.fib_eq S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw S.π_mem_fil hz hzK).symm

end PrincipalizationData

end BezoutCounterexample
