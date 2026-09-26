import BezoutCounterexample.Defs

/-!
# Section 2: the topological obstruction

* `mulVec_mem_range_parallel`: vectors in the image of `M(a,b)` (with `a² + b² = 1`) are parallel.
* `orientation_descent` (Lemma 2.1, `lem:orientation-descent`): orientability descends along
  monotone surjections between compact Hausdorff spaces.
* `IsMonotoneSurjection.comp` (Lemma 2.2, `lem:monotone-composition`).
* `Mreal_cos_sin` (equation (2.2), the half-angle formula) and `L₀_nonorientable`:
  the Möbius line bundle `L₀ = im M` on the circle `K₀` is nonorientable.
-/

noncomputable section

namespace BezoutCounterexample

open Set Topology Matrix

/-! ### Linear algebra of `M(a,b)` on the circle -/

lemma Mreal_mulVec (a b : ℝ) (w : Fin 2 → ℝ) :
    (Mreal a b).mulVec w = ![(1 + a) * w 0 + b * w 1, b * w 0 + (1 - a) * w 1] := by
  ext i
  fin_cases i <;> simp [Mreal, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Two vectors in the image of `M(a,b)`, where `a² + b² = 1`, are parallel. -/
lemma cross_eq_zero_of_mem_range {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) {p q : Fin 2 → ℝ}
    (hp : p ∈ range (Mreal a b).mulVec) (hq : q ∈ range (Mreal a b).mulVec) :
    p 0 * q 1 - p 1 * q 0 = 0 := by
  obtain ⟨w, rfl⟩ := hp
  obtain ⟨w', rfl⟩ := hq
  simp only [Mreal_mulVec, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (-(w 0 * w' 1 - w 1 * w' 0)) * hab

/-- If `p ≠ 0` and `p, q` are parallel, then `q` is a scalar multiple of `p`. -/
lemma exists_smul_of_cross_eq_zero {p q : Fin 2 → ℝ} (hp : p ≠ 0)
    (h : p 0 * q 1 - p 1 * q 0 = 0) : ∃ t : ℝ, q = t • p := by
  by_cases h0 : p 0 = 0
  · have h1 : p 1 ≠ 0 := by
      intro h1
      apply hp
      ext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨q 1 / p 1, ?_⟩
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul, h0, mul_zero]
      have : p 1 * q 0 = 0 := by rw [h0] at h; linarith
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' h1
      · exact h'
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      field_simp
  · refine ⟨q 0 / p 0, ?_⟩
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
      field_simp
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      field_simp
      linarith

/-- Two unit vectors (for any norm) in the image of `M(a,b)`, `a² + b² = 1`, agree up to sign. -/
lemma eq_or_eq_neg_of_mem_range {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) {p q : Fin 2 → ℝ}
    (hp : p ∈ range (Mreal a b).mulVec) (hq : q ∈ range (Mreal a b).mulVec)
    (hp1 : ‖p‖ = 1) (hq1 : ‖q‖ = 1) : q = p ∨ q = -p := by
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp1
  obtain ⟨t, rfl⟩ := exists_smul_of_cross_eq_zero hp0 (cross_eq_zero_of_mem_range hab hp hq)
  rw [norm_smul, hp1, mul_one, Real.norm_eq_abs] at hq1
  rcases abs_eq (zero_le_one' ℝ) |>.1 hq1 with rfl | rfl
  · left; simp
  · right; simp

lemma smul_mem_range {A : Matrix (Fin 2) (Fin 2) ℝ} {p : Fin 2 → ℝ} (hp : p ∈ range A.mulVec)
    (c : ℝ) : c • p ∈ range A.mulVec := by
  obtain ⟨w, rfl⟩ := hp
  exact ⟨c • w, Matrix.mulVec_smul A c w⟩

/-! ### Lemma 2.1: orientation descent -/

/-- **Lemma 2.1** (`lem:orientation-descent`). Let `q : K' → K` be a monotone surjection between
compact Hausdorff spaces and let `L` be the real line bundle `z ↦ im M(X z, Y z)` on `K`
(where `X² + Y² = 1`). If `q^* L` is orientable, then `L` is orientable. -/
theorem orientation_descent {K' K : Type*} [TopologicalSpace K'] [TopologicalSpace K]
    [CompactSpace K'] [T2Space K] {q : K' → K} (hq : IsMonotoneSurjection q)
    (X Y : K → ℝ) (hXY : ∀ z, X z ^ 2 + Y z ^ 2 = 1)
    (h : LineFieldOrientable (X ∘ q) (Y ∘ q)) : LineFieldOrientable X Y := by
  obtain ⟨v, hvc, hv⟩ := h
  -- normalize the section
  set u : K' → Fin 2 → ℝ := fun z => ‖v z‖⁻¹ • v z with hu_def
  have hnorm : ∀ z, ‖v z‖ ≠ 0 := fun z => norm_ne_zero_iff.2 (hv z).1
  have huc : Continuous u :=
    ((hvc.norm).inv₀ hnorm).smul hvc
  have hu1 : ∀ z, ‖u z‖ = 1 := fun z => by
    simp only [hu_def, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (hnorm z)
  have hurange : ∀ z, u z ∈ range (Mreal (X (q z)) (Y (q z))).mulVec := fun z =>
    smul_mem_range (hv z).2 _
  -- `u` is constant on fibres of `q`
  have hconst : ∀ z₁ z₂, q z₁ = q z₂ → u z₁ = u z₂ := by
    intro z₁ z₂ h12
    have hF : IsPreconnected (q ⁻¹' {q z₁}) := (hq.isConnected_fiber (q z₁)).isPreconnected
    have hT : IsDiscrete ({u z₁, -u z₁} : Set (Fin 2 → ℝ)) :=
      (Set.toFinite _).isDiscrete
    refine hF.constant_of_mapsTo hT huc.continuousOn ?_ (mem_preimage.2 rfl)
      (mem_preimage.2 h12.symm)
    intro z hz
    have hz' : q z = q z₁ := hz
    have h1 := hurange z
    have h2 := hurange z₁
    rw [hz'] at h1
    rcases eq_or_eq_neg_of_mem_range (hXY (q z₁)) h2 h1 (hu1 z₁) (hu1 z) with h | h
    · rw [h]; exact Or.inl rfl
    · rw [h]; exact Or.inr rfl
  -- descend along a set-theoretic section of `q`
  have hqs := hq.surjective
  let σ : K → K' := Function.surjInv hqs
  have hσ : ∀ z, q (σ z) = z := Function.surjInv_eq hqs
  have hquot : IsQuotientMap q :=
    IsClosedMap.isQuotientMap (hq.continuous.isClosedMap) hq.continuous hqs
  refine ⟨fun z => u (σ z), ?_, fun z => ⟨?_, ?_⟩⟩
  · rw [hquot.continuous_iff]
    convert huc using 1
    funext z
    exact hconst _ _ (hσ (q z))
  · intro h0
    have h0' : u (σ z) = 0 := h0
    have := hu1 (σ z)
    rw [h0', norm_zero] at this
    exact zero_ne_one this
  · have := hurange (σ z)
    rwa [hσ z] at this

/-! ### Lemma 2.2: composites of monotone surjections -/

/-- If `q : K' → K` is a monotone surjection from a compact space to a Hausdorff space and
`C ⊆ K` is closed and connected, then `q⁻¹(C)` is connected. -/
theorem IsMonotoneSurjection.isConnected_preimage {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space Y] {q : X → Y} (hq : IsMonotoneSurjection q)
    {C : Set Y} (hC : IsClosed C) (hCc : IsConnected C) : IsConnected (q ⁻¹' C) := by
  have hquot : IsQuotientMap q :=
    IsClosedMap.isQuotientMap (hq.continuous.isClosedMap) hq.continuous hq.surjective
  exact hquot.isCoinducing.isConnected_preimage_of_isClosed hq.isConnected_fiber hC hCc

/-- **Lemma 2.2** (`lem:monotone-composition`). A composite of monotone surjections (between
compact Hausdorff spaces) is monotone. -/
theorem IsMonotoneSurjection.comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [CompactSpace X] [T2Space Y] [T2Space Z] {q₁ : X → Y} {q₂ : Y → Z}
    (h₂ : IsMonotoneSurjection q₂) (h₁ : IsMonotoneSurjection q₁) :
    IsMonotoneSurjection (q₂ ∘ q₁) where
  continuous := h₂.continuous.comp h₁.continuous
  surjective := h₂.surjective.comp h₁.surjective
  isConnected_fiber z := by
    rw [preimage_comp]
    exact h₁.isConnected_preimage (isClosed_singleton.preimage h₂.continuous)
      (h₂.isConnected_fiber z)

/-! ### The Möbius bundle on the circle -/

/-- The half-angle formula (2.2): for `(x,y) = (cos θ, sin θ)`,
`M = 2 (cos(θ/2), sin(θ/2))ᵀ (cos(θ/2), sin(θ/2))`. -/
lemma Mreal_cos_sin (θ : ℝ) :
    Mreal (Real.cos θ) (Real.sin θ) =
      (2 : ℝ) • Matrix.vecMulVec ![Real.cos (θ / 2), Real.sin (θ / 2)]
        ![Real.cos (θ / 2), Real.sin (θ / 2)] := by
  have hc : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]; ring_nf
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have h1 := Real.sin_sq_add_cos_sq (θ / 2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mreal, hc, hs] <;> nlinarith [h1]

lemma mulVec_two_vecMulVec (c s : ℝ) (u : Fin 2 → ℝ) :
    ((2 : ℝ) • Matrix.vecMulVec ![c, s] ![c, s]).mulVec u = (2 * (c * u 0 + s * u 1)) • ![c, s] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- The point `(cos θ, sin θ)` of the circle, as a real point of `A₀`. -/
def circlePt (θ : ℝ) : RealPt A₀ :=
  RealPt.ofHom (MvPolynomial.aeval ![Real.cos θ, Real.sin θ] : A₀ →ₐ[ℚ] ℝ).toRingHom

@[simp] lemma circlePt_x (θ : ℝ) : circlePt θ x = Real.cos θ := by
  simp [circlePt, x]

@[simp] lemma circlePt_y (θ : ℝ) : circlePt θ y = Real.sin θ := by
  simp [circlePt, y]

lemma circlePt_mem (θ : ℝ) : circlePt θ ∈ K₀ := by
  show circlePt θ Δ = 0
  simp only [Δ, map_sub, map_add, map_pow, map_one, circlePt_x, circlePt_y]
  rw [Real.cos_sq_add_sin_sq]; ring

lemma continuous_circlePt : Continuous circlePt := by
  rw [RealPt.continuous_iff]
  intro p
  have : (fun θ => circlePt θ p) =
      (fun v : Fin 2 → ℝ => MvPolynomial.eval v (MvPolynomial.map (algebraMap ℚ ℝ) p)) ∘
        (fun θ => ![Real.cos θ, Real.sin θ]) := by
    funext θ
    simp [circlePt, MvPolynomial.aeval_def, MvPolynomial.eval_map]
  rw [this]
  refine (MvPolynomial.continuous_eval _).comp ?_
  refine continuous_pi fun i => ?_
  fin_cases i
  · simpa using Real.continuous_cos
  · simpa using Real.continuous_sin

/-- Every real point of `A₀` is determined by the images of `x` and `y`. -/
lemma realPt_A₀_ext {z w : RealPt A₀} (hx : z x = w x) (hy : z y = w y) : z = w := by
  have : RealPt.toHom z = RealPt.toHom w := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have h1 := eq_ratCast ((RealPt.toHom z).comp MvPolynomial.C) r
      have h2 := eq_ratCast ((RealPt.toHom w).comp MvPolynomial.C) r
      simp only [RingHom.comp_apply] at h1 h2
      rw [h1, h2]
    · intro i
      fin_cases i
      · exact hx
      · exact hy
  exact this

lemma circlePt_two_pi : circlePt (2 * Real.pi) = circlePt 0 :=
  realPt_A₀_ext (by simp) (by simp)

/-- **The Möbius line bundle `L₀ = im M` on the circle `K₀` is nonorientable.** -/
theorem L₀_nonorientable :
    ¬ LineFieldOrientable (fun z : K₀ => z.1 x) (fun z : K₀ => z.1 y) := by
  rintro ⟨v, hvc, hv⟩
  let γ : ℝ → K₀ := fun θ => ⟨circlePt θ, circlePt_mem θ⟩
  have hγ : Continuous γ := continuous_circlePt.subtype_mk _
  let w : ℝ → Fin 2 → ℝ := fun θ => ![Real.cos (θ / 2), Real.sin (θ / 2)]
  let f : ℝ → ℝ := fun θ => v (γ θ) ⬝ᵥ w θ
  have hfc : Continuous f := by
    simp only [f, dotProduct, Fin.sum_univ_two]
    fun_prop
  -- the section is `f θ • w θ`
  have hvw : ∀ θ, v (γ θ) = f θ • w θ := by
    intro θ
    obtain ⟨u, hu⟩ := (hv (γ θ)).2
    have hM : Mreal ((γ θ).1 x) ((γ θ).1 y) = Mreal (Real.cos θ) (Real.sin θ) := by
      simp [γ]
    rw [hM, Mreal_cos_sin, mulVec_two_vecMulVec] at hu
    have h1 := Real.sin_sq_add_cos_sq (θ / 2)
    have hfθ : f θ = 2 * (Real.cos (θ / 2) * u 0 + Real.sin (θ / 2) * u 1) := by
      show v (γ θ) ⬝ᵥ w θ = _
      rw [← hu]
      simp only [w, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination (2 * (Real.cos (θ / 2) * u 0 + Real.sin (θ / 2) * u 1)) * h1
    rw [hfθ, ← hu]
  have hf0 : ∀ θ, f θ ≠ 0 := by
    intro θ h
    apply (hv (γ θ)).1
    rw [hvw θ, h, zero_smul]
  have hγ2 : γ (2 * Real.pi) = γ 0 := Subtype.ext circlePt_two_pi
  have hw2 : w (2 * Real.pi) = -w 0 := by
    ext i
    fin_cases i <;> simp [w]
  have hf2 : f (2 * Real.pi) = -f 0 := by
    simp only [f, hγ2, hw2, dotProduct_neg]
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rcases lt_or_gt_of_ne (hf0 0) with hneg | hpos
  · obtain ⟨θ, -, hθ⟩ := intermediate_value_Icc h2pi hfc.continuousOn
      (show (0 : ℝ) ∈ Icc (f 0) (f (2 * Real.pi)) by rw [hf2]; constructor <;> linarith)
    exact hf0 θ hθ
  · obtain ⟨θ, -, hθ⟩ := intermediate_value_Icc' h2pi hfc.continuousOn
      (show (0 : ℝ) ∈ Icc (f (2 * Real.pi)) (f 0) by rw [hf2]; constructor <;> linarith)
    exact hf0 θ hθ

end BezoutCounterexample
