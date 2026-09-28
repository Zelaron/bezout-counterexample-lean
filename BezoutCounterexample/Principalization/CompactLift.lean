import BezoutCounterexample.Principalization.RealPts

/-! Assembly of the monotone compact lift in Lemma 4.5.
Extracted from the old Strong module; the obsolete Remark 4.7 is omitted. -/

noncomputable section

namespace BezoutCounterexample.Principalization

open LaurentPolynomial Jou IsLocalRing Topology

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)

include hd hw in
/-- The weighted sphere bundle maps monotonically onto `K` (Lemma 4.5). -/
theorem torsorK_monotone (hk2 : v₀ 1 ≠ 0) (K : Set (RealPt A)) :
    IsMonotoneSurjOn (RealPt.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)))
      (torsorK hI hmax h𝔭 hπ K) K := by
  have hmaps : Set.MapsTo (RealPt.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)))
      (torsorK hI hmax h𝔭 hπ K) K := fun w hw => hw.1
  refine ⟨hmaps, ⟨?_, ?_, ?_⟩⟩
  · exact ((RealPt.continuous_comap _).comp continuous_subtype_val).subtype_mk _
  · rintro ⟨z, hzK⟩
    rcases (gNorm_nonneg hI hmax h𝔭 (d := d) (π := π) z).lt_or_eq with hpos | h0
    · exact ⟨⟨ptA hI hmax h𝔭 hd hπ z hpos, ptA_mem hI hmax h𝔭 hd hπ K hzK hpos⟩,
        Subtype.ext (ptA_comap hI hmax h𝔭 hd hπ z hpos)⟩
    · have hz := kills_of_gNorm_zero hI hmax h𝔭 hd hw h0.symm
      obtain ⟨P⟩ := LocPres.nonempty hI hmax h𝔭 hw z hz
      have hk : 0 < P.k := by have := P.hk2 hk2; omega
      set u : ({0}ᶜ : Set (Fin P.k → ℝ)) := ⟨fun _ => 1, fun h => by
        have := congrFun h ⟨0, hk⟩; simp at this⟩
      exact ⟨⟨P.Gamma hI hmax h𝔭 hd hz hπ u, P.Gamma_mem hI hmax h𝔭 hd hz hπ hzK u⟩,
        Subtype.ext (P.Gamma_comap hI hmax h𝔭 hd hz hπ u)⟩
  · rintro ⟨z, hzK⟩
    apply isConnected_restrict_fiber
    show IsConnected (torsorFib hI hmax h𝔭 hπ K z)
    rcases (gNorm_nonneg hI hmax h𝔭 (d := d) (π := π) z).lt_or_eq with hpos | h0
    · have : torsorFib hI hmax h𝔭 hπ K z = {ptA hI hmax h𝔭 hd hπ z hpos} := by
        ext w
        constructor
        · rintro ⟨hwK, hwz⟩
          exact eq_ptA hI hmax h𝔭 hd hπ K hwK hwz hpos
        · rintro rfl
          exact ⟨ptA_mem hI hmax h𝔭 hd hπ K hzK hpos, ptA_comap hI hmax h𝔭 hd hπ z hpos⟩
      rw [this]
      exact isConnected_singleton
    · exact fib_connected hI hmax h𝔭 hd hw hπ (kills_of_gNorm_zero hI hmax h𝔭 hd hw h0.symm)
        hk2 hzK

end BezoutCounterexample.Principalization
