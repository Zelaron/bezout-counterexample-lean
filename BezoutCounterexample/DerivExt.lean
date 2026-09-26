import Mathlib

/-!
# Extending a derivation to polynomial rings, acting on coefficients

For `δ : Derivation R A A`, `mapCoeffs δ : Derivation R (MvPolynomial σ A) (MvPolynomial σ A)` applies
`δ` to every coefficient (and kills the variables).
-/

noncomputable section

namespace BezoutCounterexample

open MvPolynomial

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {σ : Type*}

/-- The `R`-linear map applying `δ` to each coefficient. -/
def mapCoeffsLin (δ : Derivation R A A) : MvPolynomial σ A →ₗ[R] MvPolynomial σ A where
  toFun p := AddMonoidAlgebra.ofCoeff (Finsupp.mapRange δ (map_zero δ) p.coeff)
  map_add' p q := by
    apply AddMonoidAlgebra.ext
    ext m
    simp
  map_smul' r p := by
    apply AddMonoidAlgebra.ext
    ext m
    simp

@[simp] lemma coeff_mapCoeffsLin (δ : Derivation R A A) (p : MvPolynomial σ A) (m : σ →₀ ℕ) :
    (mapCoeffsLin δ p).coeff m = δ (p.coeff m) := by
  simp [mapCoeffsLin]

lemma mapCoeffsLin_monomial (δ : Derivation R A A) (m : σ →₀ ℕ) (a : A) :
    mapCoeffsLin δ (monomial m a) = monomial m (δ a) := by
  classical
  ext n
  rw [coeff_mapCoeffsLin, coeff_monomial, coeff_monomial]
  split_ifs <;> simp

lemma mapCoeffsLin_mul (δ : Derivation R A A) (p q : MvPolynomial σ A) :
    mapCoeffsLin δ (p * q) = p * mapCoeffsLin δ q + q * mapCoeffsLin δ p := by
  induction p using MvPolynomial.induction_on' with
  | monomial m a =>
    induction q using MvPolynomial.induction_on' with
    | monomial n b =>
      rw [monomial_mul, mapCoeffsLin_monomial, mapCoeffsLin_monomial, mapCoeffsLin_monomial,
        monomial_mul, monomial_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add,
        add_comm m n]
    | add q₁ q₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, map_add]; ring
  | add p₁ p₂ h₁ h₂ => rw [add_mul, map_add, h₁, h₂, map_add]; ring

/-- **The coefficient-wise extension of a derivation to `MvPolynomial σ A`.** -/
def mapCoeffs (δ : Derivation R A A) : Derivation R (MvPolynomial σ A) (MvPolynomial σ A) :=
  Derivation.mk' (mapCoeffsLin δ) (fun p q => by
    rw [mapCoeffsLin_mul, smul_eq_mul, smul_eq_mul, add_comm])

@[simp] lemma mapCoeffs_C (δ : Derivation R A A) (a : A) :
    mapCoeffs (σ := σ) δ (C a) = C (δ a) :=
  mapCoeffsLin_monomial δ 0 a

@[simp] lemma mapCoeffs_X (δ : Derivation R A A) (i : σ) : mapCoeffs δ (X i : MvPolynomial σ A) = 0 := by
  show mapCoeffsLin δ (monomial (Finsupp.single i 1) 1) = 0
  rw [mapCoeffsLin_monomial, Derivation.map_one_eq_zero, monomial_zero]

end BezoutCounterexample
