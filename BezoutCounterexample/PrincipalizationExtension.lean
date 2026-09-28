import BezoutCounterexample.PrincipalizationStar

/-!
# Proposition 4.6: principalization extension

**Auxiliary assertion in the proof of Proposition 4.6**. Let `A` be a smooth finitely generated
factorial `ℚ`-domain, let `I ⊂ A` be a nonzero ideal, and let `K ⊂ Spec(A)(ℝ)` be compact. There
are a smooth finitely generated factorial `ℚ`-domain `A'`, an injection `A ↪ A'`, and a compact
set `K' ⊂ Spec(A')(ℝ)` such that `IA'` is principal and the induced map `K' → K` is a monotone
surjection.

As in the paper, this is the case `(A, I, 0)`, `N = dim A`, of the stronger assertion
`principalization_star` (`PrincipalizationStar.lean`); the triple `(A, I, 0)` satisfies
`(⋆_{dim A})` by `star_initial`.
-/

noncomputable section

namespace BezoutCounterexample

/-- **Auxiliary assertion in the proof of Proposition 4.6**. Let `A` be a smooth finitely
generated factorial `ℚ`-domain, let `I ⊂ A` be a nonzero ideal, and let `K ⊂ Spec(A)(ℝ)` be
compact. There are a smooth finitely generated factorial `ℚ`-domain `A'`, an injection
`A ↪ A'`, and a compact set `K' ⊂ Spec(A')(ℝ)` such that `IA'` is principal and the induced map
`K' → K` is a monotone surjection. -/
theorem principalization_extension_ideal (A : SmoothFactorialDomain) (I : Ideal A) (hI : I ≠ ⊥)
    (K : Set (RealPt A)) (hK : IsCompact K) :
    ∃ (A' : SmoothFactorialDomain) (f : A →ₐ[ℚ] A') (K' : Set (RealPt A')),
      Function.Injective f ∧ (I.map f).IsPrincipal ∧ IsCompact K' ∧
        IsMonotoneSurjOn (RealPt.comap (f : A →+* A')) K' K := by
  obtain ⟨N, hN⟩ := exists_ringKrullDim_eq_natCast A
  exact principalization_star N A I 0 hI (star_initial hN I) K hK

/-- **Proposition 4.6** (`prop:principalization-extension`), exactly as stated
for two elements not both zero. -/
theorem principalization_extension (A : SmoothFactorialDomain) (a b : A)
    (hab : a ≠ 0 ∨ b ≠ 0) (K : Set (RealPt A)) (hK : IsCompact K) :
    ∃ (A' : SmoothFactorialDomain) (f : A →ₐ[ℚ] A') (K' : Set (RealPt A')),
      Function.Injective f ∧ (Ideal.span {f a, f b} : Ideal A').IsPrincipal ∧
      IsCompact K' ∧ IsMonotoneSurjOn (RealPt.comap (f : A →+* A')) K' K := by
  have hI : (Ideal.span {a, b} : Ideal A) ≠ ⊥ := by
    intro h
    have ha : a = 0 := by
      have hm : a ∈ (Ideal.span {a, b} : Ideal A) := Ideal.subset_span (by simp)
      simpa [h] using hm
    have hb : b = 0 := by
      have hm : b ∈ (Ideal.span {a, b} : Ideal A) := Ideal.subset_span (by simp)
      simpa [h] using hm
    exact hab.elim (fun h => h ha) (fun h => h hb)
  obtain ⟨A', f, K', hf, hpr, hK', hmono⟩ :=
    principalization_extension_ideal A (Ideal.span {a, b}) hI K hK
  refine ⟨A', f, K', hf, ?_, hK', hmono⟩
  simpa only [Ideal.map_span, Set.image_pair] using hpr

end BezoutCounterexample
