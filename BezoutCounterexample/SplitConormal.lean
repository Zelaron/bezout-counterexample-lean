import Mathlib

/-!
# The split conormal criterion for formal smoothness

`formallySmooth_quotient_of_dual`: if `P` is formally smooth over `R` and the ideal
`K = (r₁, …, r_m)` of `P` admits derivations `Dᵢ : P → P/K` with `Dᵢ rⱼ = δᵢⱼ`, then the conormal
sequence `0 → K/K² → Ω_{P/R} ⊗ P/K → Ω_{(P/K)/R} → 0` is split exact and `P/K` is formally smooth
over `R` (Stacks, Tag 031J). This is the criterion used in Lemma 3.1(4) and Lemma 3.5(4) of the
paper.
-/

noncomputable section

namespace BezoutCounterexample

open TensorProduct

section Jacobian

variable {R P : Type*} [CommRing R] [CommRing P] [Algebra R P] {m : ℕ}

/-- **Jacobian criterion with a dual system of derivations.** If `P` is formally smooth over `R`
and `K = (r₁, …, r_m)` admits derivations `Dᵢ : P → P/K` with `Dᵢ rⱼ = δᵢⱼ`, then `P/K` is formally
smooth over `R`. -/
theorem formallySmooth_quotient_of_dual [Algebra.FormallySmooth R P] (r : Fin m → P)
    (D : Fin m → Derivation R P (P ⧸ Ideal.span (Set.range r)))
    (hD : ∀ i j, D i (r j) = if i = j then 1 else 0) :
    Algebra.FormallySmooth R (P ⧸ Ideal.span (Set.range r)) := by
  let Q := P ⧸ Ideal.span (Set.range r)
  have hsmul : ∀ (p : P) (u : Q), p • u = algebraMap P Q p * u := fun p u => Algebra.smul_def p u
  rw [Algebra.FormallySmooth.iff_split_injection (P := P) Ideal.Quotient.mk_surjective]
  set K' := RingHom.ker (algebraMap P Q)
  have hK : K' = Ideal.span (Set.range r) := Ideal.mk_ker
  let eK : Q ≃+* P ⧸ K' := Ideal.quotEquivOfEq hK.symm
  have heK : ∀ p : P, eK (algebraMap P Q p) = Ideal.Quotient.mk K' p :=
    fun p => Ideal.quotEquivOfEq_mk hK.symm p
  have hrK : ∀ j, r j ∈ K' := fun j => by rw [hK]; exact Ideal.subset_span ⟨j, rfl⟩
  let rC : Fin m → K'.Cotangent := fun j => K'.toCotangent ⟨r j, hrK j⟩
  let l₀ : Ω[P⁄R] →ₗ[P] K'.Cotangent :=
    { toFun := fun ω => ∑ i, eK ((D i).liftKaehlerDifferential ω) • rC i
      map_add' := fun ω ω' => by
        simp only [map_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun p ω => by
        simp only [map_smul, RingHom.id_apply, Finset.smul_sum, hsmul, map_mul, heK, mul_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul] }
  let lB : Q →ₗ[P] Ω[P⁄R] →ₗ[P] K'.Cotangent :=
    LinearMap.mk₂ P (fun u ω => eK u • l₀ ω)
      (fun u u' ω => by simp only [map_add, add_smul])
      (fun p u ω => by
        rw [hsmul, map_mul, heK, mul_smul, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul])
      (fun u ω ω' => by simp only [map_add, smul_add])
      (fun p u ω => by rw [map_smul, smul_comm])
  refine ⟨TensorProduct.lift lB, ?_⟩
  apply LinearMap.ext
  intro t
  obtain ⟨y, rfl⟩ := K'.toCotangent_surjective t
  rw [LinearMap.comp_apply, KaehlerDifferential.kerCotangentToTensor_toCotangent,
    TensorProduct.lift.tmul, LinearMap.id_apply]
  show eK 1 • l₀ (KaehlerDifferential.D R P y) = _
  rw [map_one, one_smul]
  show ∑ i, eK ((D i).liftKaehlerDifferential (KaehlerDifferential.D R P y)) • rC i = _
  simp only [Derivation.liftKaehlerDifferential_comp_D]
  obtain ⟨y, hy⟩ := y
  have hy' : y ∈ Ideal.span (Set.range r) := by rw [← hK]; exact hy
  -- write `y = ∑ cⱼ rⱼ`
  obtain ⟨cf, hcf⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hy'
  have hr0 : ∀ j, algebraMap P Q (r j) = 0 := fun j =>
    (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.subset_span ⟨j, rfl⟩)
  have hDy : ∀ i, D i y = algebraMap P Q (cf i) := by
    intro i
    rw [← hcf, map_sum]
    simp only [Derivation.leibniz, hsmul, hr0, hD]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; rw [ite_eq_right (Ne.symm hb)]; simp
    · simp
  simp only [hDy, heK]
  have : (⟨y, hy⟩ : K') = ∑ i, cf i • (⟨r i, hrK i⟩ : K') := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul]
    exact hcf.symm
  rw [this, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  rfl

end Jacobian

end BezoutCounterexample
