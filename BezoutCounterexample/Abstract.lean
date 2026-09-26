import BezoutCounterexample.Couchot

/-!
# Abstract forms of the obstruction and of Construction 5.1

Remark 5.4 (`rem:abstract`) of the paper.

The proof of Theorem 1.1 uses much less than Construction 5.1 provides.

* **Möbius tests** (`HasMobiusTest`): a continuous family `γ : T → Spec(B)(ℝ)` of real points with
  `Δ ∘ γ = 0` along which the Möbius line field `im M` is not orientable. Equivalently
  (`hasMobiusTest_iff`), the Möbius line field on the whole real locus `V(Δ)(ℝ)` is not orientable;
  this is the weakest invariant of this kind. A test rules out `e · (p, q) M (u, v)ᵀ = 1 + Δ c` in
  `B` (`HasMobiusTest.no_unit_value_mod`), and tests descend along ring maps
  (`HasMobiusTest.comap`).
* **Odd loops** (`not_lineFieldOrientable_of_odd_loop`, `HasOddLoop`, `hasOddLoop_iff`): a loop in
  `V(Δ)(ℝ)` on which `(x, y)` has odd degree gives a test, and its image is a compact set as in the
  paper (`exists_compact_of_odd_loop`). Angle functions always exist (`exists_angle_lift`) and
  their winding does not depend on the choice (`angle_winding_eq`), so "odd degree" is intrinsic.
* **Locally Möbius rings** (`LocallyMobius`): every finite family of elements comes from a subring
  with a test. Over such a ring, `M` has no Smith normal form and `Δ` is not a unit, so the ring is
  not an elementary divisor domain; a locally Möbius Bézout domain does not have countable
  character (Corollary 6.4).
* **Möbius towers** (`IsMobiusTower`, `IsMobiusTower.main`): Theorem 1.1 holds for the direct limit
  of any directed system of domains with injective maps, Bézout exhaustion and a test at every
  stage. No smoothness, factoriality or finiteness of the stages is needed, and the tests at
  different stages need not be compatible; tests at cofinally many stages suffice
  (`IsMobiusTower.of_cofinal`).
* **Construction 5.1 with arbitrary choices** (`isMobiusTower_of_monotone`,
  `isMobiusTower_of_sequence`): any sequence `A₀ ↪ A₁ ↪ ⋯` with compact sets `Kₙ`, monotone
  surjections `K₀ → circle` and `Kₙ₊₁ → Kₙ`, and Bézout exhaustion. This covers every run of
  Construction 5.1, whatever choices are made. The ring `R` of `Construction.lean` is an instance
  (`R.isMobiusTower`), and so is any tower with odd loops at every stage
  (`isMobiusTower_of_odd_loops`).
-/

noncomputable section

namespace BezoutCounterexample

open Set Topology

/-! ### Möbius tests -/

/-- A *Möbius test* for a ring `B` with a map `ι : A₀ → B`: a topological space `T` and a
continuous family `γ : T → Spec(B)(ℝ)` of real points on which `Δ` vanishes, such that the
pullback along `γ` of the Möbius line field `z ↦ im M(z)` is not orientable. -/
def HasMobiusTest (B : Type) [CommRing B] (ι : A₀ →+* B) : Prop :=
  ∃ (T : Type) (_ : TopologicalSpace T) (γ : T → RealPt B), Continuous γ ∧
    (∀ t, γ t (ι Δ) = 0) ∧ ¬ LineFieldOrientable (fun t => γ t (ι x)) (fun t => γ t (ι y))

/-- The real points of `Δ = 0` in `Spec(B)(ℝ)`. -/
def circleLocus (B : Type) [CommRing B] (ι : A₀ →+* B) : Set (RealPt B) := {z | z (ι Δ) = 0}

/-- **The weakest form of the invariant.** A Möbius test exists iff the Möbius line field on the
whole real locus of `Δ = 0` in `Spec(B)(ℝ)` has no continuous nowhere vanishing section. -/
theorem hasMobiusTest_iff (B : Type) [CommRing B] (ι : A₀ →+* B) :
    HasMobiusTest B ι ↔ ¬ LineFieldOrientable (fun z : circleLocus B ι => z.1 (ι x))
      (fun z : circleLocus B ι => z.1 (ι y)) := by
  constructor
  · rintro ⟨T, _, γ, hγ, hΔ, hno⟩ ⟨v, hv, hv'⟩
    exact hno ⟨fun t => v ⟨γ t, hΔ t⟩, hv.comp (hγ.subtype_mk _), fun t => hv' _⟩
  · intro h
    exact ⟨circleLocus B ι, inferInstance, Subtype.val, continuous_subtype_val, fun z => z.2, h⟩

/-- The paper's form of the invariant: a set of real points over the circle on which the Möbius
bundle is not orientable (compactness is not needed here). -/
theorem hasMobiusTest_of_set {B : Type} [CommRing B] {ι : A₀ →+* B} (K : Set (RealPt B))
    (hK : ∀ z ∈ K, z (ι Δ) = 0)
    (h : ¬ LineFieldOrientable (fun z : K => z.1 (ι x)) (fun z : K => z.1 (ι y))) :
    HasMobiusTest B ι :=
  ⟨K, inferInstance, Subtype.val, continuous_subtype_val, fun z => hK z.1 z.2, h⟩

/-- Möbius tests pull back along ring maps compatible with `A₀` (they descend a tower). -/
theorem HasMobiusTest.comap {B C : Type} [CommRing B] [CommRing C] {ιB : A₀ →+* B} (φ : B →+* C)
    (h : HasMobiusTest C (φ.comp ιB)) : HasMobiusTest B ιB := by
  obtain ⟨T, _, γ, hγ, hΔ, hno⟩ := h
  exact ⟨T, inferInstance, fun t => RealPt.comap φ (γ t), (RealPt.continuous_comap φ).comp hγ,
    fun t => hΔ t, hno⟩

/-- **The obstruction in a single ring.** If `B` has a Möbius test, then for no
`p, q, u, v, e, c ∈ B` is `e · (p, q) M (u, v)ᵀ = 1 + Δ c`: at the points of the test,
`t ↦ M(t) (u(t), v(t))ᵀ` would be a nowhere vanishing section of the pulled back Möbius bundle. -/
theorem HasMobiusTest.no_unit_value_mod {B : Type} [CommRing B] {ι : A₀ →+* B}
    (h : HasMobiusTest B ι) (p q u v e c : B) :
    e * (p * (1 + ι x) * u + p * ι y * v + q * ι y * u + q * (1 - ι x) * v) ≠ 1 + ι Δ * c := by
  intro hrel
  obtain ⟨T, _, γ, hγ, hΔ, hno⟩ := h
  apply hno
  refine ⟨fun t => (Mreal (γ t (ι x)) (γ t (ι y))).mulVec ![γ t u, γ t v], ?_,
    fun t => ⟨?_, ?_⟩⟩
  · have hc : ∀ a : B, Continuous fun t => γ t a := fun a => (RealPt.continuous_eval a).comp hγ
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp only [Mreal_mulVec] <;> simp <;> fun_prop
  · intro h0
    have h := congrArg (γ t) hrel
    simp only [map_mul, map_add, map_sub, map_one, hΔ t, zero_mul, add_zero] at h
    have h1 := congrFun h0 0
    have h2 := congrFun h0 1
    simp only [Mreal_mulVec, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h1 h2
    have : γ t p * ((1 + γ t (ι x)) * γ t u + γ t (ι y) * γ t v) +
        γ t q * (γ t (ι y) * γ t u + (1 - γ t (ι x)) * γ t v) = 0 := by
      rw [h1, h2]; ring
    have h' : γ t e * (γ t p * ((1 + γ t (ι x)) * γ t u + γ t (ι y) * γ t v) +
        γ t q * (γ t (ι y) * γ t u + (1 - γ t (ι x)) * γ t v)) = 1 := by
      linear_combination h
    rw [this, mul_zero] at h'
    exact zero_ne_one h'
  · exact ⟨_, rfl⟩

/-- If `B` has a Möbius test, `Δ` is not a unit of `B`. -/
theorem HasMobiusTest.not_isUnit {B : Type} [CommRing B] {ι : A₀ →+* B}
    (h : HasMobiusTest B ι) : ¬ IsUnit (ι Δ) := by
  intro hu
  obtain ⟨c, hc⟩ := hu.exists_right_inv
  apply h.no_unit_value_mod 0 0 0 0 0 (-c)
  linear_combination hc

end BezoutCounterexample

namespace BezoutCounterexample

open Set Topology

/-! ### Odd loops -/

/-- **Odd loops obstruct orientability.** Let `X, Y : T → ℝ` be functions on a topological space
`T`. Suppose that along a loop `c : [a, b] → T` (`c b = c a`) one has `(X, Y) ∘ c = (cos φ, sin φ)`
for a continuous angle function `φ` winding an odd number of times, `φ b = φ a + (2m+1)·2π`;
that is, `(X, Y)` has odd degree on the loop. Then the line field `im M(X, Y)` on `T` has no
continuous nowhere vanishing section. -/
theorem not_lineFieldOrientable_of_odd_loop {T : Type*} [TopologicalSpace T] (X Y : T → ℝ)
    {a b : ℝ} (hab : a ≤ b) (c : ℝ → T) (hc : ContinuousOn c (Icc a b)) (hcab : c b = c a)
    (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Icc a b))
    (hX : ∀ θ ∈ Icc a b, X (c θ) = Real.cos (φ θ)) (hY : ∀ θ ∈ Icc a b, Y (c θ) = Real.sin (φ θ))
    (m : ℤ) (hodd : φ b = φ a + (2 * m + 1) * (2 * Real.pi)) :
    ¬ LineFieldOrientable X Y := by
  rintro ⟨v, hvc, hv⟩
  let w : ℝ → Fin 2 → ℝ := fun θ => ![Real.cos (φ θ / 2), Real.sin (φ θ / 2)]
  let f : ℝ → ℝ := fun θ => v (c θ) ⬝ᵥ w θ
  have hfc : ContinuousOn f (Icc a b) := by
    have h1 : ContinuousOn (fun θ => v (c θ)) (Icc a b) := hvc.comp_continuousOn hc
    have h10 : ContinuousOn (fun θ => v (c θ) 0) (Icc a b) := (continuous_apply 0).comp_continuousOn h1
    have h11 : ContinuousOn (fun θ => v (c θ) 1) (Icc a b) := (continuous_apply 1).comp_continuousOn h1
    have hc2 : ContinuousOn (fun θ => Real.cos (φ θ / 2)) (Icc a b) :=
      Real.continuous_cos.comp_continuousOn (hφ.div_const 2)
    have hs2 : ContinuousOn (fun θ => Real.sin (φ θ / 2)) (Icc a b) :=
      Real.continuous_sin.comp_continuousOn (hφ.div_const 2)
    have : f = fun θ => v (c θ) 0 * Real.cos (φ θ / 2) + v (c θ) 1 * Real.sin (φ θ / 2) := by
      funext θ
      simp [f, w, dotProduct, Fin.sum_univ_two]
    rw [this]
    exact (h10.mul hc2).add (h11.mul hs2)
  have hvw : ∀ θ ∈ Icc a b, v (c θ) = f θ • w θ := by
    intro θ hθ
    obtain ⟨u, hu⟩ := (hv (c θ)).2
    rw [hX θ hθ, hY θ hθ, Mreal_cos_sin, mulVec_two_vecMulVec] at hu
    have h1 := Real.sin_sq_add_cos_sq (φ θ / 2)
    have hfθ : f θ = 2 * (Real.cos (φ θ / 2) * u 0 + Real.sin (φ θ / 2) * u 1) := by
      show v (c θ) ⬝ᵥ w θ = _
      rw [← hu]
      simp only [w, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination (2 * (Real.cos (φ θ / 2) * u 0 + Real.sin (φ θ / 2) * u 1)) * h1
    rw [hfθ, ← hu]
  have hf0 : ∀ θ ∈ Icc a b, f θ ≠ 0 := by
    intro θ hθ h
    apply (hv (c θ)).1
    rw [hvw θ hθ, h, zero_smul]
  have hwb : w b = -w a := by
    have hb2 : φ b / 2 = (φ a / 2 + m * (2 * Real.pi)) + Real.pi := by rw [hodd]; ring
    ext i
    fin_cases i
    · simp [w, hb2, Real.cos_add_pi, Real.cos_add_int_mul_two_pi]
    · simp [w, hb2, Real.sin_add_pi, Real.sin_add_int_mul_two_pi]
  have hfb : f b = -f a := by
    simp only [f, hcab, hwb, dotProduct_neg]
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab
  rcases lt_or_gt_of_ne (hf0 a ha) with hneg | hpos
  · obtain ⟨θ, hθ, hθ0⟩ := intermediate_value_Icc hab hfc
      (show (0 : ℝ) ∈ Icc (f a) (f b) by rw [hfb]; constructor <;> linarith)
    exact hf0 θ hθ hθ0
  · obtain ⟨θ, hθ, hθ0⟩ := intermediate_value_Icc' hab hfc
      (show (0 : ℝ) ∈ Icc (f b) (f a) by rw [hfb]; constructor <;> linarith)
    exact hf0 θ hθ hθ0

/-- **Odd loops give the paper's invariant**: the image of a loop in `V(Δ)(ℝ) ⊆ Spec(B)(ℝ)` on
which `(x, y)` has odd degree is a compact set on which the Möbius bundle is not orientable. -/
theorem exists_compact_of_odd_loop {B : Type} [CommRing B] {ι : A₀ →+* B} {a b : ℝ} (hab : a ≤ b)
    (c : ℝ → RealPt B) (hc : ContinuousOn c (Icc a b)) (hcab : c b = c a)
    (hΔ : ∀ θ ∈ Icc a b, c θ (ι Δ) = 0) (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Icc a b))
    (hX : ∀ θ ∈ Icc a b, c θ (ι x) = Real.cos (φ θ))
    (hY : ∀ θ ∈ Icc a b, c θ (ι y) = Real.sin (φ θ)) (m : ℤ)
    (hodd : φ b = φ a + (2 * m + 1) * (2 * Real.pi)) :
    ∃ K : Set (RealPt B), IsCompact K ∧ (∀ z ∈ K, z (ι Δ) = 0) ∧
      ¬ LineFieldOrientable (fun z : K => z.1 (ι x)) (fun z : K => z.1 (ι y)) := by
  refine ⟨c '' Icc a b, isCompact_Icc.image_of_continuousOn hc, ?_, ?_⟩
  · rintro _ ⟨θ, hθ, rfl⟩
    exact hΔ θ hθ
  · let c' : ℝ → c '' Icc a b := fun θ => ⟨c (projIcc a b hab θ), mem_image_of_mem _ (projIcc a b hab θ).2⟩
    have hc' : Continuous c' :=
      (hc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        fun θ => (projIcc a b hab θ).2).subtype_mk _
    have hproj : ∀ θ ∈ Icc a b, (projIcc a b hab θ : ℝ) = θ := fun θ hθ => by
      rw [projIcc_of_mem hab hθ]
    refine not_lineFieldOrientable_of_odd_loop _ _ hab c' hc'.continuousOn ?_ φ hφ ?_ ?_ m hodd
    · apply Subtype.ext
      simp only [c', projIcc_right, projIcc_left, hcab]
    · intro θ hθ
      simp only [c', hproj θ hθ]
      exact hX θ hθ
    · intro θ hθ
      simp only [c', hproj θ hθ]
      exact hY θ hθ

/-- **Odd loops give Möbius tests.** -/
theorem hasMobiusTest_of_odd_loop {B : Type} [CommRing B] {ι : A₀ →+* B} {a b : ℝ} (hab : a ≤ b)
    (c : ℝ → RealPt B) (hc : ContinuousOn c (Icc a b)) (hcab : c b = c a)
    (hΔ : ∀ θ ∈ Icc a b, c θ (ι Δ) = 0) (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Icc a b))
    (hX : ∀ θ ∈ Icc a b, c θ (ι x) = Real.cos (φ θ))
    (hY : ∀ θ ∈ Icc a b, c θ (ι y) = Real.sin (φ θ)) (m : ℤ)
    (hodd : φ b = φ a + (2 * m + 1) * (2 * Real.pi)) : HasMobiusTest B ι := by
  obtain ⟨K, -, hK, hno⟩ := exists_compact_of_odd_loop hab c hc hcab hΔ φ hφ hX hY m hodd
  exact hasMobiusTest_of_set K hK hno

/-- The circle `K₀` itself: the standard loop has degree one. This recovers
`L₀_nonorientable`. -/
theorem hasMobiusTest_A₀ : HasMobiusTest A₀ (RingHom.id A₀) :=
  hasMobiusTest_of_odd_loop (le_of_lt Real.two_pi_pos) circlePt continuous_circlePt.continuousOn
    circlePt_two_pi (fun θ _ => circlePt_mem θ) id continuousOn_id (fun θ _ => circlePt_x θ)
    (fun θ _ => circlePt_y θ) 0 (by simp)

end BezoutCounterexample

namespace BezoutCounterexample

open Set Topology

/-! ### The abstract obstruction -/

/-- `D` is *locally Möbius* (over `ι : A₀ → D`): every finite family of elements of `D` comes
from a ring `B`, embedded in `D` compatibly with `A₀`, which has a Möbius test. -/
def LocallyMobius (D : Type) [CommRing D] (ι : A₀ →+* D) : Prop :=
  ∀ (k : ℕ) (v : Fin k → D), ∃ (B : Type) (_ : CommRing B) (ιB : A₀ →+* B) (φ : B →+* D),
    Function.Injective φ ∧ φ.comp ιB = ι ∧ (∀ t, v t ∈ Set.range φ) ∧ HasMobiusTest B ιB

namespace LocallyMobius

variable {D : Type} [CommRing D] {ι : A₀ →+* D}

/-- A ring with a Möbius test is locally Möbius. -/
theorem of_hasMobiusTest (h : HasMobiusTest D ι) : LocallyMobius D ι :=
  fun _ v => ⟨D, inferInstance, ι, RingHom.id D, Function.injective_id, rfl,
    fun t => ⟨v t, rfl⟩, h⟩

/-- **The obstruction**: for no `p, q, u, v, e, c ∈ D` is `e · (p, q) M (u, v)ᵀ = 1 + Δ c`. -/
theorem no_unit_value_mod (h : LocallyMobius D ι) (p q u v e c : D) :
    e * (p * (1 + ι x) * u + p * ι y * v + q * ι y * u + q * (1 - ι x) * v) ≠ 1 + ι Δ * c := by
  intro hrel
  obtain ⟨B, _, ιB, φ, hφ, hcomp, hv, htest⟩ := h 6 ![p, q, u, v, e, c]
  choose w hw using hv
  apply htest.no_unit_value_mod (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)
  apply hφ
  have hι : ∀ a, φ (ιB a) = ι a := fun a => by rw [← hcomp]; rfl
  simp only [map_mul, map_add, map_sub, map_one, hι, hw]
  simpa using hrel

/-- `Δ` is not a unit. -/
theorem not_isUnit (h : LocallyMobius D ι) : ¬ IsUnit (ι Δ) := by
  intro hu
  obtain ⟨c, hc⟩ := hu.exists_right_inv
  apply h.no_unit_value_mod 0 0 0 0 0 (-c)
  linear_combination hc

end LocallyMobius

/-- The entries of `M` generate the unit ideal over any ring receiving `A₀`. -/
theorem unimod_M {D : Type} [CommRing D] (ι : A₀ →+* D) : Unimod (M.map ι) := by
  intro I hI
  have h1 : ι (1 + x) ∈ I := by simpa [M] using hI 0 0
  have h2 : ι (1 - x) ∈ I := by simpa [M] using hI 1 1
  have h3 : ι (1 + x) + ι (1 - x) = ι (MvPolynomial.C 2) := by
    rw [← map_add]; congr 1; rw [map_ofNat]; ring
  have h4 : ι (MvPolynomial.C 2) * ι (MvPolynomial.C (1 / 2)) = 1 := by
    rw [← map_mul, ← map_mul]; norm_num
  rw [Ideal.eq_top_iff_one, ← h4, ← h3]
  exact Ideal.mul_mem_right _ _ (Ideal.add_mem _ h1 h2)

namespace LocallyMobius

variable {D : Type} [CommRing D] {ι : A₀ →+* D}

/-- **Abstract Theorem 1.1**: over a locally Möbius ring, `M` has no Smith normal form. -/
theorem not_hasSmithNormalForm (h : LocallyMobius D ι) : ¬ HasSmithNormalForm (M.map ι) := by
  intro hSNF
  obtain ⟨p, q, u, v, e, he⟩ := exists_of_hasSmithNormalForm _ (unimod_M ι) hSNF
  apply h.no_unit_value_mod p q u v e 0
  rw [mul_zero, add_zero]
  simpa [M] using he

theorem not_isElementaryDivisorDomain (h : LocallyMobius D ι) : ¬ IsElementaryDivisorDomain D :=
  fun hD => h.not_hasSmithNormalForm (hD.2 2 2 _)

/-- **Abstract Corollary 6.4**: a locally Möbius Bézout domain does not have countable
character. -/
theorem not_hasCountableCharacter [IsDomain D] [IsBezout D] (h : LocallyMobius D ι) :
    ¬ HasCountableCharacter D := fun hc =>
  h.not_hasSmithNormalForm (hasSNF_two_of_countableCharacter hc _)

/-- **Abstract Corollary 6.4, explicit form**: uncountably many maximal ideals contain
`(1 + x, y)`, and uncountably many contain `(1 - x, y)`. -/
theorem not_countable_maximal [IsDomain D] [IsBezout D] (h : LocallyMobius D ι) :
    ¬ {m : Ideal D | m.IsMaximal ∧ ι (1 + x) ∈ m ∧ ι y ∈ m}.Countable ∧
      ¬ {m : Ideal D | m.IsMaximal ∧ ι (1 - x) ∈ m ∧ ι y ∈ m}.Countable := by
  set F := M.map ι
  have hF : ¬ HasSmithNormalForm F := h.not_hasSmithNormalForm
  have hU : Unimod F := unimod_M ι
  refine ⟨?_, ?_⟩
  · have := not_countable_row_of_not_hasSNF F hU hF
    simpa [F, M] using this
  · set S := ((glSwap D : GL (Fin 2) D) : Matrix (Fin 2) (Fin 2) D)
    have hEq : MatrixEquivalent F (S * F * S) := ⟨glSwap _, glSwap _, rfl⟩
    have hF' : ¬ HasSmithNormalForm (S * F * S) := fun h => hF (h.of_equiv hEq)
    have := not_countable_row_of_not_hasSNF _ (hU.equiv hEq) hF'
    simpa [S, F, M, glSwap, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
      using this

end LocallyMobius

end BezoutCounterexample

namespace BezoutCounterexample

open Set Topology

/-! ### Abstract towers -/

section Tower

variable {I : Type} [Preorder I] [IsDirectedOrder I] (G : I → Type) [∀ i, CommRing (G i)]
  (f : ∀ i j, i ≤ j → G i →+* G j) [DirectedSystem G fun i j h => f i j h]

/-- The direct limit of the system. -/
abbrev Lim : Type := Ring.DirectLimit G fun i j h => f i j h

/-- The map from a stage to the direct limit. -/
abbrev Lim.of (i : I) : G i →+* Lim G f := Ring.DirectLimit.of G (fun i j h => f i j h) i

variable {G f}

omit [IsDirectedOrder I] [DirectedSystem G fun i j h => f i j h] in
lemma Lim.of_f {i j : I} (h : i ≤ j) (a : G i) : Lim.of G f j (f i j h a) = Lim.of G f i a :=
  Ring.DirectLimit.of_f h a

omit [IsDirectedOrder I] [DirectedSystem G fun i j h => f i j h] in
lemma Lim.of_comp {i j : I} (h : i ≤ j) : (Lim.of G f j).comp (f i j h) = Lim.of G f i :=
  RingHom.ext fun a => Lim.of_f h a

omit [DirectedSystem G fun i j h => f i j h] in
/-- Any finite family of elements of the direct limit comes from a single stage above `i₀`. -/
lemma Lim.exists_of_fin (i₀ : I) (k : ℕ) (v : Fin k → Lim G f) :
    ∃ j, i₀ ≤ j ∧ ∃ w : Fin k → G j, ∀ t, Lim.of G f j (w t) = v t := by
  have : Nonempty I := ⟨i₀⟩
  induction k with
  | zero => exact ⟨i₀, le_rfl, Fin.elim0, fun t => Fin.elim0 t⟩
  | succ k ih =>
    obtain ⟨n, hn, w, hw⟩ := ih (fun t => v t.castSucc)
    obtain ⟨m, a, ha⟩ := Ring.DirectLimit.exists_of (v (Fin.last k))
    obtain ⟨j, hnj, hmj⟩ := exists_ge_ge n m
    refine ⟨j, hn.trans hnj, Fin.lastCases (f m j hmj a) (fun t => f n j hnj (w t)), fun t => ?_⟩
    induction t using Fin.lastCases with
    | last => simp only [Fin.lastCases_last, Lim.of_f]; exact ha
    | cast t => simp only [Fin.lastCases_castSucc, Lim.of_f]; exact hw t

lemma Lim.of_injective (hf : ∀ i j h, Function.Injective (f i j h)) (i : I) :
    Function.Injective (Lim.of G f i) :=
  Ring.DirectLimit.of_injective (G := G) f hf i

omit [DirectedSystem G fun i j h => f i j h] in
/-- **Bézout exhaustion**: if every pair of elements of every stage generates a principal ideal
at some later stage, the direct limit is a Bézout ring. -/
theorem Lim.isBezout [Nonempty I] (hbez : ∀ i (a b : G i), ∃ j, ∃ h : i ≤ j,
      (Ideal.span {f i j h a, f i j h b} : Ideal (G j)).IsPrincipal) :
    IsBezout (Lim G f) := by
  rw [IsBezout.iff_span_pair_isPrincipal]
  intro a b
  obtain ⟨j, -, w, hw⟩ := Lim.exists_of_fin (Classical.arbitrary I) 2 ![a, b]
  obtain ⟨k, hjk, ⟨g, hg⟩⟩ := hbez j (w 0) (w 1)
  have hmap := congrArg (Ideal.map (Lim.of G f k)) hg
  rw [Ideal.map_span, Ideal.map_span, Set.image_pair, Set.image_singleton, Lim.of_f, Lim.of_f,
    hw 0, hw 1] at hmap
  exact ⟨⟨Lim.of G f k g, by simpa using hmap⟩⟩

/-- Direct limits of domains along injective maps are domains. -/
theorem Lim.isDomain [Nonempty I] [∀ i, IsDomain (G i)]
    (hf : ∀ i j h, Function.Injective (f i j h)) : IsDomain (Lim G f) := by
  have : Nontrivial (Lim G f) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have : Lim.of G f (Classical.arbitrary I) 0 = Lim.of G f (Classical.arbitrary I) 1 := by
      simpa using h
    exact zero_ne_one (Lim.of_injective hf _ this)
  have : NoZeroDivisors (Lim G f) := ⟨fun {a b} hab => by
      obtain ⟨n, -, w, hw⟩ := Lim.exists_of_fin (Classical.arbitrary I) 2 ![a, b]
      have ha : Lim.of G f n (w 0) = a := hw 0
      have hb : Lim.of G f n (w 1) = b := hw 1
      have : w 0 * w 1 = 0 := by
        apply Lim.of_injective hf n
        rw [map_mul, ha, hb, hab, map_zero]
      rcases mul_eq_zero.1 this with h | h
      · left; rw [← ha, h, map_zero]
      · right; rw [← hb, h, map_zero]⟩
  exact NoZeroDivisors.to_isDomain _

omit [DirectedSystem G fun i j h => f i j h] in
/-- Countable direct limits of countable rings are countable. -/
theorem Lim.countable [Nonempty I] [Countable I] [∀ i, Countable (G i)] :
    Countable (Lim G f) := by
  have : Function.Surjective fun p : Σ i, G i => Lim.of G f p.1 p.2 := by
    intro r
    obtain ⟨n, a, h⟩ := Ring.DirectLimit.exists_of r
    exact ⟨⟨n, a⟩, h⟩
  exact this.countable

/-- **Möbius tests at every stage make the direct limit locally Möbius.** -/
theorem Lim.locallyMobius (hf : ∀ i j h, Function.Injective (f i j h)) (i₀ : I)
    (ι : A₀ →+* G i₀) (htest : ∀ j (h : i₀ ≤ j), HasMobiusTest (G j) ((f i₀ j h).comp ι)) :
    LocallyMobius (Lim G f) ((Lim.of G f i₀).comp ι) := by
  intro k v
  obtain ⟨j, hj, w, hw⟩ := Lim.exists_of_fin i₀ k v
  refine ⟨G j, inferInstance, (f i₀ j hj).comp ι, Lim.of G f j, Lim.of_injective hf j, ?_,
    fun t => ⟨w t, hw t⟩, htest j hj⟩
  rw [← RingHom.comp_assoc, Lim.of_comp]

end Tower

end BezoutCounterexample

namespace BezoutCounterexample

open Set Topology

section Tower

variable {I : Type} [Preorder I] [IsDirectedOrder I] (G : I → Type) [∀ i, CommRing (G i)]
  (f : ∀ i j, i ≤ j → G i →+* G j) [DirectedSystem G fun i j h => f i j h]

/-- The hypotheses of the abstract Theorem 1.1 on a directed system `(G, f)` with an injection
`ι : A₀ ↪ G i₀`: injective transition maps, Bézout exhaustion (every pair of elements of every
stage generates a principal ideal at some later stage), and Möbius tests at every stage above
`i₀`. No smoothness, factoriality or finiteness is required of the stages. -/
structure IsMobiusTower (i₀ : I) (ι : A₀ →+* G i₀) : Prop where
  injective : ∀ i j h, Function.Injective (f i j h)
  ι_injective : Function.Injective ι
  bezout : ∀ i (a b : G i), ∃ j, ∃ h : i ≤ j,
    (Ideal.span {f i j h a, f i j h b} : Ideal (G j)).IsPrincipal
  test : ∀ j (h : i₀ ≤ j), HasMobiusTest (G j) ((f i₀ j h).comp ι)

variable {G f}

namespace IsMobiusTower

variable {i₀ : I} {ι : A₀ →+* G i₀} (hT : IsMobiusTower G f i₀ ι)
include hT

/-- The inclusion `A₀ ↪ R` into the direct limit. -/
abbrev ιR (_hT : IsMobiusTower G f i₀ ι) : A₀ →+* Lim G f := (Lim.of G f i₀).comp ι

omit [DirectedSystem G fun i j h => f i j h] in
theorem isBezout : IsBezout (Lim G f) :=
  have : Nonempty I := ⟨i₀⟩
  Lim.isBezout hT.bezout

theorem isDomain [∀ i, IsDomain (G i)] : IsDomain (Lim G f) :=
  have : Nonempty I := ⟨i₀⟩
  Lim.isDomain hT.injective

theorem locallyMobius : LocallyMobius (Lim G f) hT.ιR :=
  Lim.locallyMobius hT.injective i₀ ι hT.test

theorem ιR_injective : Function.Injective hT.ιR :=
  (Lim.of_injective hT.injective i₀).comp hT.ι_injective

theorem Δ_ne_zero : hT.ιR Δ ≠ 0 := by
  intro h
  have : (Δ : A₀) = 0 := hT.ιR_injective (by rw [h, map_zero])
  have h2 := congrArg (MvPolynomial.eval (fun _ => (0 : ℚ))) this
  simp [Δ, x, y] at h2

/-- **Theorem 1.1 for any Möbius tower**: the direct limit `R` is a Bézout domain containing
`A₀ = ℚ[x,y]`, in which `Δ` is a nonzero nonunit, `M` has no Smith normal form, and which has
characteristic zero, is not an elementary divisor domain and does not have countable character
(Corollary 6.4). If the index set and the stages are countable, so is `R`. -/
theorem main [∀ i, IsDomain (G i)] :
    ∃ (_ : IsDomain (Lim G f)), IsBezout (Lim G f) ∧ Function.Injective hT.ιR ∧
      hT.ιR Δ ≠ 0 ∧ ¬ IsUnit (hT.ιR Δ) ∧ ¬ HasSmithNormalForm (M.map hT.ιR) ∧
      CharZero (Lim G f) ∧ ¬ IsElementaryDivisorDomain (Lim G f) ∧
      ¬ HasCountableCharacter (Lim G f) ∧
      ((Countable I ∧ ∀ i, Countable (G i)) → Countable (Lim G f)) := by
  have hD := hT.isDomain
  have hB := hT.isBezout
  let : Algebra ℚ (Lim G f) := (hT.ιR.comp (algebraMap ℚ A₀)).toAlgebra
  refine ⟨hD, hB, hT.ιR_injective, hT.Δ_ne_zero, hT.locallyMobius.not_isUnit,
    hT.locallyMobius.not_hasSmithNormalForm,
    charZero_of_injective_algebraMap (algebraMap ℚ (Lim G f)).injective,
    hT.locallyMobius.not_isElementaryDivisorDomain, hT.locallyMobius.not_hasCountableCharacter,
    fun ⟨_, _⟩ => ?_⟩
  have : Nonempty I := ⟨i₀⟩
  exact Lim.countable

end IsMobiusTower

end Tower

end BezoutCounterexample

namespace BezoutCounterexample

open Set Topology

section Tower

variable {I : Type} [Preorder I] {G : I → Type} [∀ i, CommRing (G i)]
  {f : ∀ i j, i ≤ j → G i →+* G j} [DirectedSystem G fun i j h => f i j h]

lemma dir_self (i : I) (a : G i) : f i i le_rfl a = a :=
  DirectedSystem.map_self (f := fun i j h => ⇑(f i j h)) a

lemma dir_map_map {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (a : G i) :
    f j k hjk (f i j hij a) = f i k (hij.trans hjk) a :=
  DirectedSystem.map_map (f := fun i j h => ⇑(f i j h)) hij hjk a

end Tower

lemma realPt_Δ {B : Type} [CommRing B] (φ : A₀ →+* B) (z : RealPt B) :
    z (φ Δ) = z (φ x) ^ 2 + z (φ y) ^ 2 - 1 := by
  simp [Δ, map_sub, map_add, map_pow, map_one]

/-! ### Construction 5.1 with arbitrary choices -/

section Construction

variable {G : ℕ → Type} [∀ n, CommRing (G n)] {f : ∀ i j, i ≤ j → G i →+* G j}
  [DirectedSystem G fun i j h => f i j h]

/-- **The paper's invariant propagates**: compact sets `K n` with `K 0 → K₀` and
`K (n+1) → K n` monotone surjections are Möbius tests at every stage (Lemma 2.1 and (5.2)). -/
theorem hasMobiusTest_of_monotone (ι : A₀ →+* G 0) (K : ∀ n, Set (RealPt (G n)))
    (hK : ∀ n, IsCompact (K n)) (hK0 : IsMonotoneSurjOn (RealPt.comap ι) (K 0) K₀)
    (hmono : ∀ n, IsMonotoneSurjOn (RealPt.comap (f n (n + 1) n.le_succ)) (K (n + 1)) (K n))
    (n : ℕ) :
    (∀ z ∈ K n, z (f 0 n n.zero_le (ι Δ)) = 0) ∧
      ¬ LineFieldOrientable (fun z : K n => z.1 (f 0 n n.zero_le (ι x)))
        (fun z : K n => z.1 (f 0 n n.zero_le (ι y))) := by
  induction n with
  | zero =>
    simp only [dir_self]
    refine ⟨fun z hz => hK0.1 hz, ?_⟩
    have := nonorientable_pullback ι x y (hK 0) hK0
      (fun z hz => by
        have h := realPt_Δ (RingHom.id A₀) z
        have hz' : z Δ = 0 := hz
        simp only [RingHom.id_apply] at h
        linarith)
      L₀_nonorientable
    simpa using this
  | succ n ih =>
    have hcomp : ∀ a : A₀, f 0 (n + 1) (n + 1).zero_le (ι a) =
        f n (n + 1) n.le_succ (f 0 n n.zero_le (ι a)) := fun a => (dir_map_map _ _ _).symm
    simp only [hcomp]
    refine ⟨fun z hz => ih.1 _ ((hmono n).1 hz), ?_⟩
    have := nonorientable_pullback (f n (n + 1) n.le_succ) (f 0 n n.zero_le (ι x))
      (f 0 n n.zero_le (ι y)) (hK (n + 1)) (hmono n)
      (fun z hz => by
        have h1 := ih.1 z hz
        have := realPt_Δ ((f 0 n n.zero_le).comp ι) z
        simp only [RingHom.comp_apply] at this
        linarith)
      ih.2
    simpa using this

/-- **Construction 5.1 with arbitrary choices.** Let `G 0 → G 1 → ⋯` be an `ℕ`-indexed directed
system with injective maps, `ι : A₀ ↪ G 0`, and `K n ⊆ Spec(G n)(ℝ)` compact sets such that
* `K 0` maps monotonically onto the circle `K₀` (for instance `G 0 = A₀` and `K 0 = K₀`),
* each `K (n+1)` maps monotonically onto `K n`, and
* every pair of elements of every stage generates a principal ideal at some later stage.
Then this is a Möbius tower, so Theorem 1.1 (and Corollary 6.4) hold for `R = ⋃ G n`.

Every run of Construction 5.1 produces such data, whatever extensions and compact sets
Proposition 4.6 provides at each step, whatever enumeration of the pairs is used, and however
many pairs are processed per stage. -/
theorem isMobiusTower_of_monotone (hf : ∀ i j h, Function.Injective (f i j h))
    (ι : A₀ →+* G 0) (hι : Function.Injective ι) (K : ∀ n, Set (RealPt (G n)))
    (hK : ∀ n, IsCompact (K n)) (hK0 : IsMonotoneSurjOn (RealPt.comap ι) (K 0) K₀)
    (hmono : ∀ n, IsMonotoneSurjOn (RealPt.comap (f n (n + 1) n.le_succ)) (K (n + 1)) (K n))
    (hbez : ∀ i (a b : G i), ∃ j, ∃ h : i ≤ j,
      (Ideal.span {f i j h a, f i j h b} : Ideal (G j)).IsPrincipal) :
    IsMobiusTower G f 0 ι where
  injective := hf
  ι_injective := hι
  bezout := hbez
  test j _ := by
    obtain ⟨h1, h2⟩ := hasMobiusTest_of_monotone ι K hK hK0 hmono j
    exact hasMobiusTest_of_set (K j) h1 h2

end Construction

end BezoutCounterexample

namespace BezoutCounterexample

open Set Topology

/-! ### Odd loops at every stage -/

/-- `B` contains an *odd loop*: a loop `c : [a, b] → Spec(B)(ℝ)` along which
`(x, y) = (cos φ, sin φ)` (so `c` lies in `V(Δ)(ℝ)`) with `φ` winding an odd number of times. -/
def HasOddLoop (B : Type) [CommRing B] (ι : A₀ →+* B) : Prop :=
  ∃ (a b : ℝ) (c : ℝ → RealPt B) (φ : ℝ → ℝ) (m : ℤ), a ≤ b ∧ ContinuousOn c (Icc a b) ∧
    c b = c a ∧ ContinuousOn φ (Icc a b) ∧
    (∀ θ ∈ Icc a b, c θ (ι x) = Real.cos (φ θ) ∧ c θ (ι y) = Real.sin (φ θ)) ∧
    φ b = φ a + (2 * m + 1) * (2 * Real.pi)

theorem HasOddLoop.hasMobiusTest {B : Type} [CommRing B] {ι : A₀ →+* B}
    (h : HasOddLoop B ι) : HasMobiusTest B ι := by
  obtain ⟨a, b, c, φ, m, hab, hc, hcab, hφ, hxy, hodd⟩ := h
  refine hasMobiusTest_of_odd_loop hab c hc hcab (fun θ hθ => ?_) φ hφ (fun θ hθ => (hxy θ hθ).1)
    (fun θ hθ => (hxy θ hθ).2) m hodd
  rw [realPt_Δ, (hxy θ hθ).1, (hxy θ hθ).2, Real.cos_sq_add_sin_sq]
  ring

/-- **Theorem 1.1 from odd loops.** Bézout exhaustion together with an odd loop at every stage
(no compatibility between the loops of different stages is needed) gives a Möbius tower. -/
theorem isMobiusTower_of_odd_loops {I : Type} [Preorder I] {G : I → Type}
    [∀ i, CommRing (G i)] {f : ∀ i j, i ≤ j → G i →+* G j}
    [DirectedSystem G fun i j h => f i j h] (hf : ∀ i j h, Function.Injective (f i j h))
    (i₀ : I) (ι : A₀ →+* G i₀) (hι : Function.Injective ι)
    (hbez : ∀ i (a b : G i), ∃ j, ∃ h : i ≤ j,
      (Ideal.span {f i j h a, f i j h b} : Ideal (G j)).IsPrincipal)
    (hloop : ∀ j (h : i₀ ≤ j), HasOddLoop (G j) ((f i₀ j h).comp ι)) :
    IsMobiusTower G f i₀ ι :=
  ⟨hf, hι, hbez, fun j h => (hloop j h).hasMobiusTest⟩

/-! ### Towers from successive maps -/

section Seq

variable {G : ℕ → Type} [∀ n, CommRing (G n)] (g : ∀ n, G n →+* G (n + 1))

/-- The composite `G i → G j` (`i ≤ j`) of the successive maps of a sequence of rings. -/
def seqMap {i j : ℕ} (h : i ≤ j) (a : G i) : G j :=
  Nat.leRecOn h (fun {k} (b : G k) => g k b) a

lemma seqMap_self (i : ℕ) (a : G i) : seqMap g (le_refl i) a = a := Nat.leRecOn_self _

lemma seqMap_succ {i j : ℕ} (h : i ≤ j) (a : G i) :
    seqMap g (h.trans (Nat.le_succ j)) a = g j (seqMap g h a) := Nat.leRecOn_succ h _

lemma seqMap_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (a : G i) :
    seqMap g (hij.trans hjk) a = seqMap g hjk (seqMap g hij a) := Nat.leRecOn_trans hij hjk _

/-- The composite `G i → G j` as a ring homomorphism. -/
def seqHom (i j : ℕ) (h : i ≤ j) : G i →+* G j where
  toFun := seqMap g h
  map_one' := by
    induction j, h using Nat.le_induction with
    | base => exact seqMap_self g i 1
    | succ k hik ih => rw [seqMap_succ g hik, ih, map_one]
  map_mul' a b := by
    induction j, h using Nat.le_induction with
    | base => simp only [seqMap_self]
    | succ k hik ih => rw [seqMap_succ g hik, seqMap_succ g hik, seqMap_succ g hik, ih, map_mul]
  map_zero' := by
    induction j, h using Nat.le_induction with
    | base => exact seqMap_self g i 0
    | succ k hik ih => rw [seqMap_succ g hik, ih, map_zero]
  map_add' a b := by
    induction j, h using Nat.le_induction with
    | base => simp only [seqMap_self]
    | succ k hik ih => rw [seqMap_succ g hik, seqMap_succ g hik, seqMap_succ g hik, ih, map_add]

instance seqHom.directedSystem : DirectedSystem G fun i j h => ⇑(seqHom g i j h) where
  map_self i a := seqMap_self g i a
  map_map _ _ _ hij hjk a := (seqMap_trans g hij hjk a).symm

lemma seqHom_succ (n : ℕ) : seqHom g n (n + 1) n.le_succ = g n :=
  RingHom.ext fun a => (seqMap_succ g (le_refl n) a).trans (congrArg _ (seqMap_self g n a))

lemma seqHom_injective (hg : ∀ n, Function.Injective (g n)) (i j : ℕ) (h : i ≤ j) :
    Function.Injective (seqHom g i j h) :=
  Nat.leRecOn_injective h _ (fun k => hg k)

/-- **Construction 5.1 with arbitrary choices, for a sequence of injections**
`G 0 ↪ G 1 ↪ ⋯` (this is literally the output of Construction 5.1). -/
theorem isMobiusTower_of_sequence (hg : ∀ n, Function.Injective (g n))
    (ι : A₀ →+* G 0) (hι : Function.Injective ι) (K : ∀ n, Set (RealPt (G n)))
    (hK : ∀ n, IsCompact (K n)) (hK0 : IsMonotoneSurjOn (RealPt.comap ι) (K 0) K₀)
    (hmono : ∀ n, IsMonotoneSurjOn (RealPt.comap (g n)) (K (n + 1)) (K n))
    (hbez : ∀ i (a b : G i), ∃ j, ∃ h : i ≤ j,
      (Ideal.span {seqHom g i j h a, seqHom g i j h b} : Ideal (G j)).IsPrincipal) :
    IsMobiusTower G (seqHom g) 0 ι :=
  isMobiusTower_of_monotone (seqHom_injective g hg) ι hι K hK hK0
    (fun n => by rw [seqHom_succ]; exact hmono n) hbez

end Seq

end BezoutCounterexample

namespace BezoutCounterexample

open Set Topology

/-! ### The ring `R` of Construction 5.1 is a Möbius tower -/

namespace R

variable (hPE : CoprimePairPE)

/-- Bézout exhaustion for Construction 5.1. -/
theorem bezout_exhaustion (m : ℕ) (a b : G hPE m) : ∃ j, ∃ h : m ≤ j,
    (Ideal.span {transHom hPE m j h a, transHom hPE m j h b} : Ideal (G hPE j)).IsPrincipal := by
  obtain ⟨j, hj⟩ := e_diag_surjective hPE m (a, b)
  set n := Nat.pair m j
  have hmn : m ≤ n := Nat.left_le_pair m j
  have hpair : (stage hPE n).pair n = (transHom hPE m n hmn a, transHom hPE m n hmn b) := by
    rw [Stage.pair, Nat.unpair_pair, e_transport hPE m j n hmn, hj]
    rfl
  have hprinc := (step hPE n (stage hPE n)).principal
  rw [hpair] at hprinc
  refine ⟨n + 1, hmn.trans n.le_succ, ?_⟩
  have h1 : ∀ c : G hPE m, transHom hPE m (n + 1) (hmn.trans n.le_succ) c =
      trans hPE n (transHom hPE m n hmn c) := fun c => transLE_succ hPE hmn c
  rw [h1, h1]
  exact hprinc

lemma transHom_comp_ι (j : ℕ) (h : 0 ≤ j) :
    (transHom hPE 0 j h).comp ((stage hPE 0).ι : A₀ →+* G hPE 0) =
      ((stage hPE j).ι : A₀ →+* G hPE j) := by
  induction j with
  | zero => exact RingHom.ext fun a => transLE_self hPE 0 _
  | succ j ih =>
    refine RingHom.ext fun a => ?_
    have h1 : transHom hPE 0 (j + 1) h ((stage hPE 0).ι a) =
        trans hPE j (transHom hPE 0 j j.zero_le ((stage hPE 0).ι a)) :=
      transLE_succ hPE j.zero_le _
    rw [RingHom.comp_apply, AlgHom.coe_toRingHom, h1, ι_succ]
    have h2 := congrArg (fun φ : A₀ →+* G hPE j => φ a) (ih j.zero_le)
    simp only [RingHom.comp_apply, AlgHom.coe_toRingHom] at h2
    rw [h2]
    rfl

/-- **The ring `R` of Construction 5.1 is a Möbius tower**, with the compact sets `Kₙ` as
Möbius tests. -/
theorem isMobiusTower :
    IsMobiusTower (G hPE) (transHom hPE) 0 ((stage hPE 0).ι : A₀ →+* G hPE 0) where
  injective := transHom_injective hPE
  ι_injective := (stage hPE 0).ι_injective
  bezout := bezout_exhaustion hPE
  test j h := by
    rw [transHom_comp_ι hPE j h]
    exact hasMobiusTest_of_set _ (fun z hz => (stage hPE j).K_circle z hz)
      (stage hPE j).nonorientable

/-- The abstract theorem recovers Theorem 1.1 for `R`. -/
example : ¬ HasSmithNormalForm (M.map (ι hPE)) :=
  (isMobiusTower hPE).locallyMobius.not_hasSmithNormalForm

end R

end BezoutCounterexample

namespace BezoutCounterexample

open Set Topology

/-! ### Degrees of loops: angle functions exist and their winding is well defined -/

/-- The point `(X, Y)` of the unit circle as an element of `Circle`. -/
def circleOf (X Y : ℝ) (h : X ^ 2 + Y ^ 2 = 1) : Circle :=
  ⟨X + Y * Complex.I, by
    have : Complex.normSq (X + Y * Complex.I) = 1 := by
      rw [Complex.normSq_add_mul_I]; linarith
    rw [Submonoid.unitSphere, Submonoid.mem_mk, Subsemigroup.mem_mk, mem_sphere_zero_iff_norm,
      Complex.norm_def, this, Real.sqrt_one]⟩

lemma exp_eq_circleOf {φ X Y : ℝ} (h : X ^ 2 + Y ^ 2 = 1) (he : Circle.exp φ = circleOf X Y h) :
    X = Real.cos φ ∧ Y = Real.sin φ := by
  have h' := congrArg (fun z : Circle => (z : ℂ)) he
  simp only [Circle.coe_exp, circleOf] at h'
  have hre := congrArg Complex.re h'
  have him := congrArg Complex.im h'
  simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im] at hre him
  exact ⟨hre.symm, him.symm⟩

/-- **Angle functions exist**: a continuous map `[a, b] → S¹` has a continuous lift to `ℝ`
(path lifting for the covering `exp : ℝ → S¹`). -/
theorem exists_angle_lift {a b : ℝ} (hab : a ≤ b) {X Y : ℝ → ℝ} (hX : ContinuousOn X (Icc a b))
    (hY : ContinuousOn Y (Icc a b)) (h1 : ∀ θ ∈ Icc a b, X θ ^ 2 + Y θ ^ 2 = 1) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧ ∀ θ ∈ Icc a b, X θ = Real.cos (φ θ) ∧ Y θ = Real.sin (φ θ) := by
  -- reparametrize `[a, b]` by the unit interval
  let θt : unitInterval → ℝ := fun t => a + (t : ℝ) * (b - a)
  have hθt : ∀ t, θt t ∈ Icc a b := fun t => ⟨by nlinarith [t.2.1, t.2.2], by nlinarith [t.2.1, t.2.2]⟩
  have hθc : Continuous θt := by fun_prop
  let γ : C(unitInterval, Circle) := ⟨fun t => circleOf (X (θt t)) (Y (θt t)) (h1 _ (hθt t)), by
    apply Continuous.subtype_mk
    have hXc : Continuous fun t => X (θt t) := hX.comp_continuous hθc hθt
    have hYc : Continuous fun t => Y (θt t) := hY.comp_continuous hθc hθt
    exact (Complex.continuous_ofReal.comp hXc).add
      ((Complex.continuous_ofReal.comp hYc).mul continuous_const)⟩
  obtain ⟨e, he⟩ := Circle.exp_surjective (γ 0)
  obtain ⟨Γ, hΓ, -⟩ := Circle.isCoveringMap_exp.exists_path_lifts γ e he.symm
  -- back to `[a, b]`
  let tθ : ℝ → unitInterval := fun θ => Set.projIcc 0 1 zero_le_one ((θ - a) / (b - a))
  have htc : Continuous tθ := continuous_projIcc.comp (by fun_prop)
  refine ⟨fun θ => Γ (tθ θ), Γ.continuous.comp htc, fun θ hθ => ?_⟩
  have hθ' : θt (tθ θ) = θ := by
    rcases hab.eq_or_lt with rfl | hlt
    · simp only [θt, sub_self, mul_zero, add_zero]
      exact le_antisymm hθ.1 hθ.2
    · have hba : (0 : ℝ) < b - a := sub_pos.2 hlt
      have hmem : (θ - a) / (b - a) ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (sub_nonneg.2 hθ.1) hba.le,
          (div_le_one hba).2 (by linarith [hθ.2])⟩
      simp only [θt, tθ, Set.projIcc_of_mem zero_le_one hmem]
      field_simp
      ring
  have := congrFun hΓ (tθ θ)
  simp only [Function.comp_apply] at this
  have h2 := exp_eq_circleOf (h1 _ (hθt (tθ θ))) this
  rw [hθ'] at h2
  exact h2

/-- **The winding of an angle function is well defined**: two continuous angle functions of the
same map `[a, b] → S¹` have the same total variation `φ b - φ a`. -/
theorem angle_winding_eq {a b : ℝ} (hab : a ≤ b) {φ ψ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc a b))
    (hψ : ContinuousOn ψ (Icc a b)) (hc : ∀ θ ∈ Icc a b, Real.cos (φ θ) = Real.cos (ψ θ))
    (hs : ∀ θ ∈ Icc a b, Real.sin (φ θ) = Real.sin (ψ θ)) : φ b - φ a = ψ b - ψ a := by
  have hint : ∀ θ ∈ Icc a b, ∃ m : ℤ, (φ θ - ψ θ) / (2 * Real.pi) = m := by
    intro θ hθ
    have he : Circle.exp (φ θ) = Circle.exp (ψ θ) := by
      apply Circle.ext
      simp only [Circle.coe_exp]
      apply Complex.ext <;>
        simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, hc θ hθ, hs θ hθ]
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 he
    refine ⟨m, ?_⟩
    rw [hm]
    field_simp
    ring
  set g : ℝ → ℝ := fun θ => (φ θ - ψ θ) / (2 * Real.pi)
  have hg : ContinuousOn g (Icc a b) := (hφ.sub hψ).div_const _
  obtain ⟨m, hm⟩ := hint a ⟨le_rfl, hab⟩
  obtain ⟨n, hn⟩ := hint b ⟨hab, le_rfl⟩
  have hmn : m = n := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨θ, hθ, hθv⟩ := intermediate_value_Icc hab hg
        (show (m : ℝ) + 1 / 2 ∈ Icc (g a) (g b) by
          simp only [g, hm, hn]
          have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hlt
          constructor <;> linarith)
      obtain ⟨k, hk⟩ := hint θ hθ
      have : (k : ℝ) = m + 1 / 2 := hk ▸ hθv
      have h2 : (2 * k : ℝ) = 2 * m + 1 := by linarith
      have h3 : 2 * k = 2 * m + 1 := by exact_mod_cast h2
      omega
    · obtain ⟨θ, hθ, hθv⟩ := intermediate_value_Icc' hab hg
        (show (n : ℝ) + 1 / 2 ∈ Icc (g b) (g a) by
          simp only [g, hm, hn]
          have : (n : ℝ) + 1 ≤ m := by exact_mod_cast hlt
          constructor <;> linarith)
      obtain ⟨k, hk⟩ := hint θ hθ
      have : (k : ℝ) = n + 1 / 2 := hk ▸ hθv
      have h2 : (2 * k : ℝ) = 2 * n + 1 := by linarith
      have h3 : 2 * k = 2 * n + 1 := by exact_mod_cast h2
      omega
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have ha' : φ a - ψ a = m * (2 * Real.pi) := by rw [← hm]; field_simp
  have hb' : φ b - ψ b = n * (2 * Real.pi) := by rw [← hn]; field_simp
  rw [hmn] at ha'
  linarith

/-- **Odd degree is intrinsic**: `B` has an odd loop iff some loop in `V(Δ)(ℝ)` is such that
*every* continuous angle function of `(x, y)` along it winds an odd number of times. -/
theorem hasOddLoop_iff (B : Type) [CommRing B] (ι : A₀ →+* B) :
    HasOddLoop B ι ↔ ∃ (a b : ℝ) (c : ℝ → RealPt B), a ≤ b ∧ ContinuousOn c (Icc a b) ∧
      c b = c a ∧ (∀ θ ∈ Icc a b, c θ (ι Δ) = 0) ∧
      ∀ φ : ℝ → ℝ, ContinuousOn φ (Icc a b) →
        (∀ θ ∈ Icc a b, c θ (ι x) = Real.cos (φ θ) ∧ c θ (ι y) = Real.sin (φ θ)) →
        ∃ m : ℤ, φ b = φ a + (2 * m + 1) * (2 * Real.pi) := by
  constructor
  · rintro ⟨a, b, c, φ₀, m, hab, hc, hcab, hφ₀, hxy, hodd⟩
    refine ⟨a, b, c, hab, hc, hcab, fun θ hθ => ?_, fun φ hφ hxy' => ⟨m, ?_⟩⟩
    · rw [realPt_Δ, (hxy θ hθ).1, (hxy θ hθ).2, Real.cos_sq_add_sin_sq]
      ring
    · have := angle_winding_eq hab hφ hφ₀ (fun θ hθ => by rw [← (hxy' θ hθ).1, (hxy θ hθ).1])
        (fun θ hθ => by rw [← (hxy' θ hθ).2, (hxy θ hθ).2])
      linarith
  · rintro ⟨a, b, c, hab, hc, hcab, hΔ, hall⟩
    have hcx : ContinuousOn (fun θ => c θ (ι x)) (Icc a b) :=
      (RealPt.continuous_eval _).comp_continuousOn hc
    have hcy : ContinuousOn (fun θ => c θ (ι y)) (Icc a b) :=
      (RealPt.continuous_eval _).comp_continuousOn hc
    obtain ⟨φ, hφ, hlift⟩ := exists_angle_lift hab hcx hcy (fun θ hθ => by
      have := hΔ θ hθ
      rw [realPt_Δ] at this
      linarith)
    obtain ⟨m, hm⟩ := hall φ hφ.continuousOn hlift
    exact ⟨a, b, c, φ, m, hab, hc, hcab, hφ.continuousOn, hlift, hm⟩

end BezoutCounterexample

namespace BezoutCounterexample

open Set Topology

/-- The identity is a monotone surjection `K → K` (for instance `K₀ → K₀` when `G 0 = A₀`). -/
lemma IsMonotoneSurjOn.comap_id {A : Type} [CommRing A] (K : Set (RealPt A)) :
    IsMonotoneSurjOn (RealPt.comap (RingHom.id A)) K K :=
  IsMonotoneSurjOn.id K

/-- **Tests at cofinally many stages suffice**: they descend to all stages. -/
theorem IsMobiusTower.of_cofinal {I : Type} [Preorder I] {G : I → Type} [∀ i, CommRing (G i)]
    {f : ∀ i j, i ≤ j → G i →+* G j} [DirectedSystem G fun i j h => f i j h]
    (hf : ∀ i j h, Function.Injective (f i j h)) (i₀ : I) (ι : A₀ →+* G i₀)
    (hι : Function.Injective ι)
    (hbez : ∀ i (a b : G i), ∃ j, ∃ h : i ≤ j,
      (Ideal.span {f i j h a, f i j h b} : Ideal (G j)).IsPrincipal)
    (htest : ∀ j, i₀ ≤ j → ∃ k, j ≤ k ∧ ∃ h : i₀ ≤ k,
      HasMobiusTest (G k) ((f i₀ k h).comp ι)) :
    IsMobiusTower G f i₀ ι := by
  refine ⟨hf, hι, hbez, fun j hj => ?_⟩
  obtain ⟨k, hjk, hk, ht⟩ := htest j hj
  have hcomp : (f i₀ k hk).comp ι = (f j k hjk).comp ((f i₀ j hj).comp ι) := by
    refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply]
    exact (dir_map_map hj hjk (ι a)).symm
  rw [hcomp] at ht
  exact ht.comap (f j k hjk)

end BezoutCounterexample
