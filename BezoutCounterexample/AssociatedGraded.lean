import BezoutCounterexample.Rees

/-!
# The associated graded ring in Lemma 3.5(5)

The earlier project constructed the additive isomorphism. Here we equip the
direct sum of the subquotients with its ring structure and check explicitly
that `[f]ₐ [g]ᵦ = [fg]ₐ₊ᵦ`. Thus the displayed identification is a ring
isomorphism, and the entire associated graded ring is a domain.
-/

noncomputable section

namespace BezoutCounterexample.ReesData

open LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A]
  [Algebra.Smooth ℚ A] (S : ReesData A)

/-- The direct sum `⊕ⱼ 𝓕ⱼ/𝓕ⱼ₊₁`, with the multiplication specified below. -/
def AssociatedGraded : Type := DirectSum ℕ S.grPiece

/-- Additive identification with `𝓡/(s)` before transporting multiplication. -/
def gradedEquiv : S.AssociatedGraded ≃ (S.𝓡 ⧸ Ideal.span {S.s}) :=
  S.quotientSEquiv.toEquiv

instance : CommRing S.AssociatedGraded := S.gradedEquiv.commRing

/-- Lemma 3.5(5), as a ring isomorphism. -/
def quotientSRingEquiv : S.AssociatedGraded ≃+* (S.𝓡 ⧸ Ideal.span {S.s}) :=
  S.gradedEquiv.ringEquiv

/-- The additive group is the usual direct sum of the graded pieces. -/
def gradedAddEquiv : (DirectSum ℕ S.grPiece) ≃+ S.AssociatedGraded :=
  S.quotientSEquiv.toAddEquiv.trans S.quotientSRingEquiv.symm.toAddEquiv

@[simp] theorem gradedAddEquiv_apply (a : DirectSum ℕ S.grPiece) :
    S.gradedAddEquiv a = a := S.quotientSEquiv.symm_apply_apply a

/-- A homogeneous element, represented by `f ∈ 𝓕ⱼ`. -/
def initialForm (j : ℕ) (f : A) (hf : f ∈ S.𝓕 j) : S.AssociatedGraded :=
  DirectSum.of S.grPiece j (Submodule.Quotient.mk ⟨f, hf⟩)

@[simp] theorem quotientSRingEquiv_initialForm (j : ℕ) (f : A) (hf : f ∈ S.𝓕 j) :
    S.quotientSRingEquiv (S.initialForm j f hf) =
      Ideal.Quotient.mk _ (S.mono j f hf) := by
  change S.gradedToQuot (DirectSum.of S.grPiece j (Submodule.Quotient.mk ⟨f, hf⟩)) = _
  rw [gradedToQuot, ← DirectSum.lof_eq_of A, DirectSum.toModule_lof, grToQuot_mk]

/-- Multiplicativity of the filtration. -/
theorem mul_mem_filtration {a b : ℕ} {f g : A}
    (hf : f ∈ S.𝓕 a) (hg : g ∈ S.𝓕 b) : f * g ∈ S.𝓕 (a + b) := by
  simpa only [Nat.cast_add, S.fil_F] using
    S.fil.mul_le a b (Ideal.mul_mem_mul
      (by simpa only [S.fil_F] using hf) (by simpa only [S.fil_F] using hg))

/-- The ring structure is the usual multiplication of initial forms. -/
theorem initialForm_mul {a b : ℕ} {f g : A}
    (hf : f ∈ S.𝓕 a) (hg : g ∈ S.𝓕 b) :
    S.initialForm a f hf * S.initialForm b g hg =
      S.initialForm (a + b) (f * g) (S.mul_mem_filtration hf hg) := by
  apply S.quotientSRingEquiv.injective
  rw [map_mul, quotientSRingEquiv_initialForm, quotientSRingEquiv_initialForm,
    quotientSRingEquiv_initialForm, ← map_mul]
  congr 1
  apply Subtype.ext
  change (C f * T (a : ℤ)) * (C g * T (b : ℤ)) = C (f * g) * T ((a + b : ℕ) : ℤ)
  rw [map_mul, Nat.cast_add, T_add]
  ring

/-- The identity is the degree-zero initial form of `1`. -/
@[simp] theorem initialForm_one (h1 : (1 : A) ∈ S.𝓕 0) :
    S.initialForm 0 1 h1 = 1 := by
  apply S.quotientSRingEquiv.injective
  rw [quotientSRingEquiv_initialForm, map_one]
  have hm : S.mono 0 1 h1 = 1 := by
    apply Subtype.ext
    simp [mono]
  simp only [Nat.cast_zero, hm, map_one]

/-- The associated graded ring is a domain, including arbitrary finite sums
of homogeneous elements (Lemma 3.5(5)). -/
theorem associatedGraded_isDomain : IsDomain S.AssociatedGraded := by
  let : IsDomain (S.𝓡 ⧸ Ideal.span {S.s}) := S.isDomain_quotient_s
  exact S.quotientSRingEquiv.injective.isDomain S.quotientSRingEquiv.toRingHom

end BezoutCounterexample.ReesData
