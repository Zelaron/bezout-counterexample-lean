import BezoutCounterexample.Principalization.Transfer

/-!
# Charts at points of smooth algebras

* `Chart.basis`: the differentials of a chart form a basis of `Ω[R⁄ℚ]`.
* `Chart.isCentred_of_mem`: a chart whose functions lie in `𝔪` of a formally smooth Noetherian
  local `ℚ`-algebra is centred.
* `Chart.exists_centred`: centred charts exist when the residue field is separable.

Foundations for Theorem 3.3 (`thm:invariant`) of the paper.
-/

noncomputable section


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {R : Type*} [CommRing R] [Algebra ℚ R] {n : ℕ}

namespace Chart

variable (c : Chart R n)

/-- The differentials of a chart form a basis of `Ω[R⁄ℚ]`. -/
def basis : Module.Basis (Fin n) R Ω[R⁄ℚ] :=
  Module.Basis.mk (v := fun i => KaehlerDifferential.D ℚ R (c.x i))
    (by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have := congrArg (c.d i).liftKaehlerDifferential hg
      simp only [map_sum, map_smul, Derivation.liftKaehlerDifferential_comp_D, c.d_x, smul_eq_mul,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_zero] at this
      exact this)
    (by rw [c.span])

@[simp] lemma basis_apply (i : Fin n) : c.basis i = KaehlerDifferential.D ℚ R (c.x i) := by
  simp [basis]

end Chart

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing TensorProduct

variable {R : Type*} [CommRing R] [Algebra ℚ R] {n : ℕ} [IsLocalRing R]

/-- For a formally smooth local `ℚ`-algebra with formally smooth residue field, the conormal map
`𝔪/𝔪² → κ ⊗ Ω` is injective. -/
lemma conormal_injective [Algebra.FormallySmooth ℚ R]
    [Algebra.FormallySmooth ℚ (ResidueField R)] :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor ℚ R (ResidueField R)) := by
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := ℚ) (P := R)
    (A := ResidueField R) (residue_surjective)).1 inferInstance
  exact Function.LeftInverse.injective (g := l) fun x => by
    rw [← LinearMap.comp_apply, hl, LinearMap.id_apply]

/-- An element of `𝔪` whose differential vanishes in `κ ⊗ Ω` lies in `𝔪²`. -/
lemma mem_sq_of_tmul_eq_zero [Algebra.FormallySmooth ℚ R]
    [Algebra.FormallySmooth ℚ (ResidueField R)] {r : R} (hr : r ∈ maximalIdeal R)
    (h : (1 : ResidueField R) ⊗ₜ[R] KaehlerDifferential.D ℚ R r = 0) :
    r ∈ maximalIdeal R ^ 2 := by
  have hrk : r ∈ RingHom.ker (algebraMap R (ResidueField R)) := by
    rw [show algebraMap R (ResidueField R) = residue R from rfl, ker_residue]; exact hr
  have h0 : (RingHom.ker (algebraMap R (ResidueField R))).toCotangent ⟨r, hrk⟩ = 0 := by
    apply conormal_injective
    rw [KaehlerDifferential.kerCotangentToTensor_toCotangent, map_zero]
    exact h
  rw [Ideal.toCotangent_eq_zero] at h0
  have h1 : r ∈ (RingHom.ker (algebraMap R (ResidueField R))) ^ 2 := h0
  rwa [show algebraMap R (ResidueField R) = residue R from rfl, ker_residue] at h1

namespace Chart

variable {c : Chart R n}

/-- A chart whose functions lie in `𝔪` is centred. -/
theorem isCentred_of_mem [IsNoetherianRing R] [Algebra.FormallySmooth ℚ R]
    [Algebra.FormallySmooth ℚ (ResidueField R)] (hx : ∀ i, c.x i ∈ maximalIdeal R) :
    c.IsCentred := by
  refine le_antisymm ?_ ((Ideal.span_le).2 (by rintro _ ⟨i, rfl⟩; exact hx i))
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
    (maximalIdeal_le_jacobson _) ?_
  intro r hr
  set r' := r - ∑ i, c.d i r * c.x i with hr'
  have hr'm : r' ∈ maximalIdeal R :=
    sub_mem hr (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hx i))
  have hd : ∀ l, c.d l r' ∈ maximalIdeal R := by
    intro l
    have : ∀ i, c.d l (c.d i r * c.x i) =
        (if l = i then c.d i r else 0) + c.x i * c.d l (c.d i r) := by
      intro i
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, c.d_x, mul_ite, mul_one, mul_zero]
    rw [hr', map_sub, map_sum]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [sub_add_cancel_left]
    exact neg_mem (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hx i))
  have h2 : r' ∈ maximalIdeal R ^ 2 := by
    refine mem_sq_of_tmul_eq_zero hr'm ?_
    rw [c.kD_eq_sum r', tmul_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← TensorProduct.smul_tmul]
    rw [show (c.d l r' • (1 : ResidueField R)) = 0 from by
      rw [Algebra.smul_def, mul_one]; exact (residue_eq_zero_iff _).2 (hd l)]
    rw [zero_tmul]
  have : r = r' + ∑ i, c.d i r * c.x i := by rw [hr']; ring
  rw [this]
  refine add_mem (Submodule.mem_sup_right ?_) (Submodule.mem_sup_left (Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)))
  rw [smul_eq_mul, ← pow_two]; exact h2

end Chart

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R] {n : ℕ} [IsLocalRing R]

namespace Chart

/-- **Recentring.** Replacing each chart function by its image under the minimal polynomial of its
residue gives a centred chart; functions already in `𝔪` are unchanged. -/
theorem exists_centred [IsNoetherianRing R] [Algebra.FormallySmooth ℚ R]
    [Algebra.FormallySmooth ℚ (ResidueField R)] [Algebra.IsIntegral ℚ (ResidueField R)]
    (c : Chart R n) :
    ∃ c' : Chart R n, c'.IsCentred ∧ ∀ i, c.x i ∈ maximalIdeal R → c'.x i = c.x i := by
  classical
  set P : Fin n → ℚ[X] := fun i => minpoly ℚ (residue R (c.x i)) with hP
  set y : Fin n → R := fun i => aeval (c.x i) (P i) with hy
  have hsep : ∀ i, (P i).Separable := fun i =>
    Algebra.IsSeparable.isSeparable ℚ (residue R (c.x i))
  have hmap : ∀ (a : R) (p : ℚ[X]), residue R (aeval a p) = aeval (residue R a) p := fun a p =>
    (Polynomial.aeval_algebraMap_apply (B := ResidueField R) a p).symm
  have hres : ∀ i, residue R (aeval (c.x i) (derivative (P i))) ≠ 0 := by
    intro i
    rw [hmap]
    exact (hsep i).aeval_derivative_ne_zero (minpoly.aeval ℚ _)
  have hjac : c.jac y = Matrix.diagonal fun j => aeval (c.x j) (derivative (P j)) := by
    ext i j
    simp only [jac, Matrix.of_apply, hy, Derivation.map_aeval, c.d_x, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  have hdet : IsUnit (c.jac y).det := by
    rw [hjac, Matrix.det_diagonal, IsUnit.prod_univ_iff]
    intro j
    rw [← notMem_maximalIdeal, ← residue_eq_zero_iff]; exact hres j
  refine ⟨c.change y hdet, isCentred_of_mem fun i => ?_, fun i hi => ?_⟩
  · rw [change_x, ← residue_eq_zero_iff, hy]
    simp only
    rw [hmap]
    exact minpoly.aeval ℚ _
  · rw [change_x, hy]
    simp only [hP, (residue_eq_zero_iff _).2 hi, minpoly.zero, aeval_X]

end Chart

end BezoutCounterexample.Principalization

