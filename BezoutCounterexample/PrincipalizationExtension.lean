import BezoutCounterexample.PrincipalizationStar

/-!
# Proposition 4.6: principalization extension

**Proposition 4.6** (`prop:principalization-extension`). Let `A` be a smooth finitely generated
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

/-- **Proposition 4.6** (`prop:principalization-extension`). Let `A` be a smooth finitely
generated factorial `ℚ`-domain, let `I ⊂ A` be a nonzero ideal, and let `K ⊂ Spec(A)(ℝ)` be
compact. There are a smooth finitely generated factorial `ℚ`-domain `A'`, an injection
`A ↪ A'`, and a compact set `K' ⊂ Spec(A')(ℝ)` such that `IA'` is principal and the induced map
`K' → K` is a monotone surjection. -/
theorem principalization_extension (A : SmoothFactorialDomain) (I : Ideal A) (hI : I ≠ ⊥)
    (K : Set (RealPt A)) (hK : IsCompact K) :
    ∃ (A' : SmoothFactorialDomain) (f : A →ₐ[ℚ] A') (K' : Set (RealPt A')),
      Function.Injective f ∧ (I.map f).IsPrincipal ∧ IsCompact K' ∧
        IsMonotoneSurjOn (RealPt.comap (f : A →+* A')) K' K := by
  obtain ⟨N, hN⟩ := exists_ringKrullDim_eq_natCast A
  exact principalization_star N A I 0 hI (star_initial hN I) K hK

end BezoutCounterexample
