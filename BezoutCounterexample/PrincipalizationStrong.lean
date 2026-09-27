import BezoutCounterexample.Principalization.Strong

/-!
# Remark 4.7: further properties of the principalization extension

**Remark 4.7** (`rem:strong`). The construction of Proposition 4.6 also has the following
properties (`principalization_extension_strong`).

1. If `z ∈ K` and `z(f) ≠ 0` for some `f ∈ I`, then the fibre of `K' → K` over `z` is a single
   point. (In a torsor step this holds because `I ⊆ 𝔭`, and the lifted point lies outside the
   zero set of `I₁`, since `f = s^d · f T^d`; in a divisorial step `K` is unchanged.) Moreover,
   `K' → K` restricts to a homeomorphism from the preimage of `K ∖ V(I)(ℝ)` onto `K ∖ V(I)(ℝ)`.
2. The homomorphism `A → A'` is of finite presentation and smooth away from `V(I)`: for every
   prime `P` of `A'` not containing `IA'`, the local ring `A'_P` is formally smooth over `A`; in
   particular `A → A'[1/f]` is smooth for `f ∈ I`.

The proof runs the induction of Proposition 4.6 with these extra properties
(`Principalization.principalizationExtension_strong`: in a torsor step, `f ∈ I ⊆ 𝔭` gives
`f^j ∈ 𝓕_j`, hence `𝓡[1/f] = A[1/f][T, T⁻¹]`, and `U[1/f]` is a Jouanolou ring over it).
-/

noncomputable section

namespace BezoutCounterexample

/-- **Remark 4.7** (`rem:strong`): Proposition 4.6 with the additional properties (1) and (2). -/
theorem principalization_extension_strong (A : SmoothFactorialDomain) (I : Ideal A)
    (hI : I ≠ ⊥) (K : Set (RealPt A)) (hK : IsCompact K) :
    ∃ (A' : SmoothFactorialDomain) (f : A →ₐ[ℚ] A') (K' : Set (RealPt A')),
      Function.Injective f ∧ (I.map f).IsPrincipal ∧ IsCompact K' ∧
      ∃ hmono : IsMonotoneSurjOn (RealPt.comap (f : A →+* A')) K' K,
        -- (1): singleton fibres off `V(I)(ℝ)`, and a homeomorphism there
        (∀ z ∈ K, (∃ a ∈ I, z a ≠ 0) →
          ∃! z' : RealPt A', z' ∈ K' ∧ RealPt.comap (f : A →+* A') z' = z) ∧
        IsHomeomorph (({z : K | ∃ a ∈ I, z.1 a ≠ 0}).restrictPreimage
          (hmono.1.restrict (RealPt.comap (f : A →+* A')) K' K)) ∧
        -- (2): finite presentation, and smoothness away from `V(I)`
        (f : A →+* A').FinitePresentation ∧
        (∀ (P : Ideal A') [P.IsPrime], ¬ I.map f ≤ P →
          ((algebraMap A' (Localization.AtPrime P)).comp (f : A →+* A')).FormallySmooth) ∧
        (∀ a ∈ I, ((algebraMap A' (Localization.Away (f a))).comp (f : A →+* A')).Smooth) := by
  obtain ⟨A', f, K', t, hinj, ht, hK', hmono, hia, hhom, hfp, hsa, hsm, -⟩ :=
    Principalization.principalizationExtension_strong A I K hI hK
  refine ⟨A', f, K', hinj, ⟨⟨t, ht⟩⟩, hK', hmono, ?_, hhom hmono.1, hfp, hsa, hsm⟩
  intro z hzK ⟨a, ha, hza⟩
  obtain ⟨⟨z', hz'⟩, hz'z⟩ := hmono.2.surjective ⟨z, hzK⟩
  have hz'z' : RealPt.comap (f : A →+* A') z' = z := congrArg Subtype.val hz'z
  refine ⟨z', ⟨hz', hz'z'⟩, fun w ⟨hw, hwz⟩ => ?_⟩
  refine hia w hw z' hz' (hwz.trans hz'z'.symm) ⟨a, ha, ?_⟩
  show RealPt.comap (f : A →+* A') w a ≠ 0
  rw [hwz]; exact hza

end BezoutCounterexample
