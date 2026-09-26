import BezoutCounterexample.MainTheorem

/-!
# Proposition 6.1 (`prop:quotient-module`): a nonfree rank-one projective module

Let `B = R/(Δ)` and let `Π = ½ M̄ ∈ M₂(B)`. Then `Π` is idempotent, and `Π B²` is a projective
`B`-module of constant rank one (its fibre `κ(p) ⊗ Π B²` is one-dimensional at every prime `p`)
that is not free.

The general linear algebra (ranks of images of idempotent `2 × 2` matrices, and the trace
argument showing that a free module of this kind has rank one) is developed for an arbitrary
commutative ring first.
-/

noncomputable section

namespace BezoutCounterexample

open Module TensorProduct

/-! ### Images of idempotent matrices -/

section Idempotent

variable {B : Type*} [CommRing B] (E : Matrix (Fin 2) (Fin 2) B)

/-- The module `Π B²`, the image of the idempotent `Π` (called `E` in the code). -/
abbrev imageModule : Submodule B (Fin 2 → B) := LinearMap.range E.mulVecLin

/-- The projection `B² → E B²`. -/
def projIm : (Fin 2 → B) →ₗ[B] imageModule E := E.mulVecLin.rangeRestrict

variable {E}

lemma projIm_comp_subtype (hE : E * E = E) :
    projIm E ∘ₗ (imageModule E).subtype = LinearMap.id := by
  ext ⟨v, w, rfl⟩ : 1
  apply Subtype.ext
  simp only [projIm, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply,
    LinearMap.codRestrict_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hE]

lemma subtype_comp_projIm : (imageModule E).subtype ∘ₗ projIm E = E.mulVecLin := by
  ext v : 1
  simp [projIm]

/-- `E B²` is projective (a direct summand of `B²`). -/
theorem imageModule_projective (hE : E * E = E) : Module.Projective B (imageModule E) :=
  Module.Projective.of_split _ _ (projIm_comp_subtype hE)

lemma rank_pos_of_ne_zero' {k : Type*} [Field k] {A : Matrix (Fin 2) (Fin 2) k} (h : A ≠ 0) :
    0 < A.rank := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  apply h
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  ext i j
  have := congrArg (fun f => f (Pi.single j 1) i) h0
  simpa [Matrix.mulVec_single] using this

/-- An idempotent `2 × 2` matrix of trace one over a field has rank one. -/
theorem rank_eq_one_of_idempotent {k : Type*} [Field k] {A : Matrix (Fin 2) (Fin 2) k}
    (hA : A * A = A) (htr : A.trace = 1) : A.rank = 1 := by
  have h1 : A * (1 - A) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hA, sub_self]
  have hsum := Matrix.rank_add_rank_le_card_of_mul_eq_zero h1
  have hA0 : A ≠ 0 := by
    intro h; rw [h, Matrix.trace_zero] at htr; exact zero_ne_one htr
  have hB0 : (1 - A) ≠ 0 := by
    intro h
    have := congrArg Matrix.trace h
    rw [Matrix.trace_sub, htr, Matrix.trace_one, Matrix.trace_zero, Fintype.card_fin] at this
    norm_num at this
  have r1 := rank_pos_of_ne_zero' hA0
  have r2 := rank_pos_of_ne_zero' hB0
  simp only [Fintype.card_fin] at hsum
  omega

variable (k : Type*) [Field k] [Algebra B k]

lemma piScalarRight_comp_baseChange :
    (piScalarRight B k k (Fin 2)).toLinearMap ∘ₗ E.mulVecLin.baseChange k =
      (E.map (algebraMap B k)).mulVecLin ∘ₗ (piScalarRight B k k (Fin 2)).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c w
  funext i
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.baseChange_tmul, piScalarRight_apply, piScalarRightHom_tmul,
    Matrix.mulVecLin_apply]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply,
    Algebra.smul_def, map_add, map_mul]
  ring

/-- The fibre of `E B²` over a field `k` has dimension `rank Π_k`. -/
theorem finrank_baseChange_imageModule (hE : E * E = E) :
    finrank k (k ⊗[B] imageModule E) = (E.map (algebraMap B k)).rank := by
  set i := (imageModule E).subtype
  set s := projIm E
  set ik := i.baseChange k
  set sk := s.baseChange k
  have hsik : sk ∘ₗ ik = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, projIm_comp_subtype hE, LinearMap.baseChange_id]
  have hinj : Function.Injective ik := by
    intro a b hab
    have := congrArg sk hab
    rwa [← LinearMap.comp_apply, hsik, ← LinearMap.comp_apply, hsik] at this
  have hrange : LinearMap.range ik = LinearMap.range (E.mulVecLin.baseChange k) := by
    rw [← subtype_comp_projIm, LinearMap.baseChange_comp]
    apply le_antisymm
    · have : ik = (ik ∘ₗ sk) ∘ₗ ik := by rw [LinearMap.comp_assoc, hsik, LinearMap.comp_id]
      conv_lhs => rw [this]
      exact LinearMap.range_comp_le_range _ _
    · exact LinearMap.range_comp_le_range _ _
  rw [← LinearMap.finrank_range_of_inj hinj, hrange]
  set e := piScalarRight B k k (Fin 2)
  rw [← LinearEquiv.finrank_map_eq e, ← LinearMap.range_comp, piScalarRight_comp_baseChange,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range e)]
  rfl

/-- The trace argument: if `E B²` is free, then (over a nontrivial `ℚ`-algebra) it is free of
rank one, and `E = v λ` with `λ v = 1`. -/
theorem exists_factorization_of_free [Nontrivial B] [Algebra ℚ B] (hE : E * E = E)
    (htr : E.trace = 1) [Module.Free B (imageModule E)] :
    ∃ v l : Fin 2 → B, (∀ i j, E i j = v i * l j) ∧ l 0 * v 0 + l 1 * v 1 = 1 := by
  have hCZ : CharZero B := charZero_of_injective_algebraMap (algebraMap ℚ B).injective
  have : Module.Finite B (imageModule E) := Module.Finite.range _
  set r := finrank B (imageModule E)
  let b := Module.finBasis B (imageModule E)
  set s := projIm E
  have hsi : ∀ p : imageModule E, s p = p := fun p =>
    congrArg (fun f => f p) (projIm_comp_subtype hE)
  -- the columns of `E`
  have hcol : ∀ j, (s (Pi.single j 1) : Fin 2 → B) = fun i => E i j := by
    intro j
    funext i
    simp [s, projIm, Matrix.mulVec_single]
  -- the trace of `E` is the rank `r`
  have htrace : (r : B) = 1 := by
    rw [← htr]
    have h1 : ∀ j, E j j = ∑ l, b.repr (s (Pi.single j 1)) l * (b l : Fin 2 → B) j := by
      intro j
      have := congrArg (fun p : imageModule E => (p : Fin 2 → B) j)
        (b.sum_repr (s (Pi.single j 1)))
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at this
      rw [this, hcol]
    rw [Matrix.trace]
    simp only [Matrix.diag_apply]
    rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_comm]
    have h2 : ∀ l, ∑ j, b.repr (s (Pi.single j 1)) l * (b l : Fin 2 → B) j = 1 := by
      intro l
      have hb : (b l : Fin 2 → B) = ∑ j, (b l : Fin 2 → B) j • Pi.single j 1 := by
        funext i; simp [Finset.sum_apply, Pi.single_apply]
      have : ∑ j, b.repr (s (Pi.single j 1)) l * (b l : Fin 2 → B) j =
          b.repr (s (b l : Fin 2 → B)) l := by
        conv_rhs => rw [hb]
        simp [mul_comm]
      rw [this, hsi, b.repr_self, Finsupp.single_eq_same]
    simp [h2, r]
  have hr : r = 1 := by exact_mod_cast htrace
  -- the rank-one factorization
  let i0 : Fin r := ⟨0, by omega⟩
  refine ⟨(b i0 : Fin 2 → B), fun j => b.repr (s (Pi.single j 1)) i0, ?_, ?_⟩
  · intro i j
    have huniq : ∀ l : Fin r, l = i0 := fun l => Fin.ext (by omega)
    have := congrArg (fun p : imageModule E => (p : Fin 2 → B) i)
      (b.sum_repr (s (Pi.single j 1)))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at this
    rw [hcol] at this
    simp only at this
    show E i j = (b i0 : Fin 2 → B) i * b.repr (s (Pi.single j 1)) i0
    rw [← this, Fintype.sum_eq_single i0 (fun l hl => absurd (huniq l) hl), mul_comm]
  · have hb : (b i0 : Fin 2 → B) = ∑ j, (b i0 : Fin 2 → B) j • Pi.single j 1 := by
      funext i; simp [Finset.sum_apply, Pi.single_apply]
    have : b.repr (s (Pi.single 0 1)) i0 * (b i0 : Fin 2 → B) 0 +
        b.repr (s (Pi.single 1 1)) i0 * (b i0 : Fin 2 → B) 1 = b.repr (s (b i0 : Fin 2 → B)) i0 := by
      conv_rhs => rw [hb]
      simp [mul_comm, Fin.sum_univ_two]
    rw [this, hsi, b.repr_self, Finsupp.single_eq_same]

end Idempotent

/-! ### The module over `R/(Δ)` -/

/-- The matrix `½ M` over `A₀`. -/
def Mhalf : Matrix (Fin 2) (Fin 2) A₀ := (MvPolynomial.C (2⁻¹ : ℚ) : A₀) • M

lemma Mhalf_sq : Mhalf * Mhalf - Mhalf =
    ((MvPolynomial.C (2⁻¹ : ℚ) : A₀) ^ 2 * Δ) • (1 : Matrix (Fin 2) (Fin 2) A₀) := by
  have h2 : 2 * (MvPolynomial.C (2⁻¹ : ℚ) : A₀) = 1 := by
    rw [show (2 : A₀) = MvPolynomial.C 2 by rw [map_ofNat], ← map_mul]; norm_num
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Mhalf, M, Δ]
  · linear_combination ((MvPolynomial.C (2⁻¹ : ℚ) : A₀) * (1 + x)) * h2
  · linear_combination ((MvPolynomial.C (2⁻¹ : ℚ) : A₀) * y) * h2
  · linear_combination ((MvPolynomial.C (2⁻¹ : ℚ) : A₀) * y) * h2
  · linear_combination ((MvPolynomial.C (2⁻¹ : ℚ) : A₀) * (1 - x)) * h2

lemma Mhalf_trace : Mhalf.trace = 1 := by
  have h2 : 2 * (MvPolynomial.C (2⁻¹ : ℚ) : A₀) = 1 := by
    rw [show (2 : A₀) = MvPolynomial.C 2 by rw [map_ofNat], ← map_mul]; norm_num
  simp [Mhalf, M, Matrix.trace_fin_two]
  linear_combination h2

variable (hPE : CoprimePairPE)

/-- The ring `B = R/(Δ)`. -/
abbrev Bq : Type := R hPE ⧸ Ideal.span {R.ι hPE Δ}

/-- The quotient map `R → B`. -/
abbrev πq : R hPE →+* Bq hPE := Ideal.Quotient.mk _

/-- The idempotent `E = ½ M̄ ∈ M₂(B)`. -/
def Piq : Matrix (Fin 2) (Fin 2) (Bq hPE) := Mhalf.map ((πq hPE).comp (R.ι hPE))

lemma Bq_nontrivial : Nontrivial (Bq hPE) := by
  apply Ideal.Quotient.nontrivial_iff.2
  rw [Ne, Ideal.span_singleton_eq_top]
  exact R.Δ_not_isUnit hPE

lemma πq_Δ : πq hPE (R.ι hPE Δ) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)

lemma Piq_idempotent : Piq hPE * Piq hPE = Piq hPE := by
  set φ := (πq hPE).comp (R.ι hPE)
  have h : (Mhalf * Mhalf - Mhalf).map φ =
      (((MvPolynomial.C (2⁻¹ : ℚ) : A₀) ^ 2 * Δ) • (1 : Matrix (Fin 2) (Fin 2) A₀)).map φ := by
    rw [Mhalf_sq]
  have hR : (((MvPolynomial.C (2⁻¹ : ℚ) : A₀) ^ 2 * Δ) •
      (1 : Matrix (Fin 2) (Fin 2) A₀)).map φ = 0 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Matrix.zero_apply]
    split_ifs <;> simp [φ]
  rw [hR, Matrix.map_sub _ (map_sub φ), Matrix.map_mul, sub_eq_zero] at h
  exact h

lemma Piq_trace : (Piq hPE).trace = 1 := by
  have : (Piq hPE).trace = ((πq hPE).comp (R.ι hPE)) Mhalf.trace := by
    simp [Piq, Matrix.trace]
  rw [this, Mhalf_trace, map_one]

/-- **Proposition 6.1.** `E = ½ M̄` is idempotent, and `E B²` is a projective `B`-module of
constant rank one (every fibre `κ(p) ⊗ E B²` is one-dimensional) that is not free. -/
theorem quotient_module :
    Nontrivial (Bq hPE) ∧ Piq hPE * Piq hPE = Piq hPE ∧
      Module.Projective (Bq hPE) (imageModule (Piq hPE)) ∧
      (∀ (p : Ideal (Bq hPE)) [p.IsPrime],
        finrank p.ResidueField (p.Fiber (imageModule (Piq hPE))) = 1) ∧
      ¬ Module.Free (Bq hPE) (imageModule (Piq hPE)) := by
  have hnt := Bq_nontrivial hPE
  refine ⟨hnt, Piq_idempotent hPE, imageModule_projective (Piq_idempotent hPE), ?_, ?_⟩
  · intro p _
    change finrank p.ResidueField (p.ResidueField ⊗[Bq hPE] imageModule (Piq hPE)) = 1
    rw [finrank_baseChange_imageModule _ (Piq_idempotent hPE)]
    apply rank_eq_one_of_idempotent
    · rw [← Matrix.map_mul, Piq_idempotent]
    · rw [Matrix.trace, ← map_one (algebraMap (Bq hPE) p.ResidueField), ← Piq_trace hPE,
        Matrix.trace, map_sum]
      rfl
  · intro hfree
    obtain ⟨v, l, hvl, hlv⟩ := exists_factorization_of_free (Piq_idempotent hPE) (Piq_trace hPE)
    -- lift to `R`
    obtain ⟨v', hv'⟩ : ∃ v' : Fin 2 → R hPE, ∀ i, πq hPE (v' i) = v i :=
      ⟨fun i => (Ideal.Quotient.mk_surjective (v i)).choose,
        fun i => (Ideal.Quotient.mk_surjective (v i)).choose_spec⟩
    obtain ⟨l', hl'⟩ : ∃ l' : Fin 2 → R hPE, ∀ i, πq hPE (l' i) = l i :=
      ⟨fun i => (Ideal.Quotient.mk_surjective (l i)).choose,
        fun i => (Ideal.Quotient.mk_surjective (l i)).choose_spec⟩
    -- `½ λ M v ≡ 1 (mod Δ)`
    set ι := R.ι hPE
    set h : Bq hPE := πq hPE (ι (MvPolynomial.C (2⁻¹ : ℚ)))
    have hP00 : Piq hPE 0 0 = h * πq hPE (1 + ι x) := by simp [Piq, Mhalf, M, h, ι]
    have hP01 : Piq hPE 0 1 = h * πq hPE (ι y) := by simp [Piq, Mhalf, M, h, ι]
    have hP10 : Piq hPE 1 0 = h * πq hPE (ι y) := by simp [Piq, Mhalf, M, h, ι]
    have hP11 : Piq hPE 1 1 = h * πq hPE (1 - ι x) := by simp [Piq, Mhalf, M, h, ι]
    set val := l' 0 * (1 + ι x) * v' 0 + l' 0 * ι y * v' 1 + l' 1 * ι y * v' 0 +
      l' 1 * (1 - ι x) * v' 1
    have hval : h * πq hPE val = 1 := by
      have e00 := hvl 0 0
      have e01 := hvl 0 1
      have e10 := hvl 1 0
      have e11 := hvl 1 1
      rw [hP00] at e00
      rw [hP01] at e01
      rw [hP10] at e10
      rw [hP11] at e11
      have hval' : πq hPE val = l 0 * πq hPE (1 + ι x) * v 0 + l 0 * πq hPE (ι y) * v 1 +
          l 1 * πq hPE (ι y) * v 0 + l 1 * πq hPE (1 - ι x) * v 1 := by
        simp only [val, map_add, map_mul, hv', hl']
      rw [hval']
      linear_combination (l 0 * v 0) * e00 + (l 0 * v 1) * e01 + (l 1 * v 0) * e10 +
        (l 1 * v 1) * e11 + (l 0 * v 0 + l 1 * v 1 + 1) * hlv
    have hmem : ι (MvPolynomial.C (2⁻¹ : ℚ)) * val - 1 ∈ Ideal.span {ι Δ} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one]
      exact sub_eq_zero.2 hval
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
    apply R.no_unit_value_mod hPE (l' 0) (l' 1) (v' 0) (v' 1) (ι (MvPolynomial.C (2⁻¹ : ℚ))) c
    linear_combination (-1 : R hPE) * hc

end BezoutCounterexample
