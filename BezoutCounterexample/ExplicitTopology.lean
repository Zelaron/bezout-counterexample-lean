import BezoutCounterexample.ExplicitAlgebra
import BezoutCounterexample.Construction

/-!
# Section 6.3: an explicit first extension — real points

Let `K* = {u² + v² = 1, r = u, s = v, t ≥ 0, t(2u + t) = 0} ⊂ Spec(A*)(ℝ)`. We show that `K*` is
compact, that `K* → K₀` is a monotone surjection (its fibres are points, except for the circle
over `(1, 0)`), and hence that the pullback of the Möbius bundle `L₀` to `K*` is nonorientable.

Together with `ExplicitAlgebra`, this shows that the conclusion of Proposition 4.6 holds for
`A = ℚ[x, y]`, `I = (x - 1, y)` and `K = K₀`, unconditionally
(`principalizationExtension_example`).
-/

noncomputable section

namespace BezoutCounterexample.Explicit

open Set Topology

/-! ### Coordinates of real points of `A*` -/

/-- The coordinates `(t, u, v, r, s)` of a real point of `A*`. -/
def coords (z : RealPt Astar) : Fin 5 → ℝ := ![z t, z (CS u), z (CS v), z (CS r), z (CS s)]

lemma coords_rel (z : RealPt Astar) : coords z 3 * coords z 1 + coords z 4 * coords z 2 = 1 := by
  have h := congrArg z (congrArg CS rel)
  simp only [map_add, map_mul, map_one] at h
  simpa [coords] using h

/-- A real point of `A*` is determined by its coordinates. -/
lemma realPt_Astar_ext {z w : RealPt Astar} (h : coords z = coords w) : z = w := by
  have ht : z t = w t := congrFun h 0
  have hu : z (CS u) = w (CS u) := congrFun h 1
  have hv : z (CS v) = w (CS v) := congrFun h 2
  have hr : z (CS r) = w (CS r) := congrFun h 3
  have hs : z (CS s) = w (CS s) := congrFun h 4
  have hS : (RealPt.toHom z).comp CS = (RealPt.toHom w).comp CS := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro q
      have h1 := eq_ratCast (((RealPt.toHom z).comp CS).comp (Ideal.Quotient.mk _) |>.comp
        MvPolynomial.C) q
      have h2 := eq_ratCast (((RealPt.toHom w).comp CS).comp (Ideal.Quotient.mk _) |>.comp
        MvPolynomial.C) q
      simp only [RingHom.comp_apply] at h1 h2 ⊢
      rw [h1, h2]
    · intro i
      fin_cases i
      · exact hu
      · exact hs
      · exact hr
      · exact hv
  have : RealPt.toHom z = RealPt.toHom w := by
    apply MvPolynomial.ringHom_ext
    · intro a
      exact congrArg (fun φ : S →+* ℝ => φ a) hS
    · intro i
      fin_cases i
      exact ht
  exact this

/-! ### Evaluation at points of `{r u + s v = 1} ⊂ ℝ⁵` -/

/-- The subspace `{p ∈ ℝ⁵ : r u + s v = 1}` (coordinates `p = (t, u, v, r, s)`). -/
abbrev Ksub : Type := {p : Fin 5 → ℝ // p 3 * p 1 + p 4 * p 2 = 1}

/-- The coordinate functions on `Ksub`. -/
def coordFn (i : Fin 5) : C(Ksub, ℝ) :=
  ⟨fun p => p.1 i, (continuous_apply i).comp continuous_subtype_val⟩

lemma coordFn_rel : coordFn 3 * coordFn 1 + coordFn 4 * coordFn 2 = 1 := by
  ext p
  simpa [coordFn] using p.2

/-- `A* → C(Ksub, ℝ)`. -/
def Φ : Astar →+* C(Ksub, ℝ) :=
  MvPolynomial.eval₂Hom (evalS (coordFn 1) (coordFn 2) (coordFn 3) (coordFn 4) coordFn_rel).toRingHom
    (fun _ => coordFn 0)

/-- The real point of `A*` corresponding to `p ∈ Ksub`. -/
def evalPtStar (p : Ksub) : RealPt Astar :=
  RealPt.ofHom ((Pi.evalRingHom (fun _ : Ksub => ℝ) p).comp (ContinuousMap.coeFnRingHom.comp Φ))

lemma evalPtStar_apply (p : Ksub) (F : Astar) : evalPtStar p F = Φ F p := rfl

lemma continuous_evalPtStar : Continuous evalPtStar :=
  RealPt.continuous_iff.2 fun F => (Φ F).continuous

lemma coords_evalPtStar (p : Ksub) : coords (evalPtStar p) = p.1 := by
  funext i
  fin_cases i <;> simp [coords, evalPtStar_apply, Φ, t, coordFn]

/-- Every real point of `A*` comes from a point of `Ksub`. -/
lemma eq_evalPtStar (z : RealPt Astar) : z = evalPtStar ⟨coords z, coords_rel z⟩ :=
  realPt_Astar_ext (by rw [coords_evalPtStar])

/-! ### The compact set `K*` -/

/-- The conditions defining `K*`, in coordinates `(t, u, v, r, s)`. -/
def KboxProp (p : Fin 5 → ℝ) : Prop :=
  p 1 ^ 2 + p 2 ^ 2 = 1 ∧ p 3 = p 1 ∧ p 4 = p 2 ∧ 0 ≤ p 0 ∧ p 0 * (2 * p 1 + p 0) = 0

/-- `K* = {u² + v² = 1, r = u, s = v, t ≥ 0, t(2u + t) = 0} ⊂ Spec(A*)(ℝ)`. -/
def Kstar : Set (RealPt Astar) := {z | KboxProp (coords z)}

lemma Kstar_eq_image : Kstar = evalPtStar '' {p : Ksub | KboxProp p.1} := by
  ext z
  constructor
  · intro hz
    exact ⟨⟨coords z, coords_rel z⟩, hz, (eq_evalPtStar z).symm⟩
  · rintro ⟨p, hp, rfl⟩
    show KboxProp (coords (evalPtStar p))
    rw [coords_evalPtStar]
    exact hp

/-- `K*` is closed and bounded: `|u|, |v|, |r|, |s| ≤ 1` and `0 ≤ t ≤ 2`; hence compact. -/
theorem isCompact_Kstar : IsCompact Kstar := by
  rw [Kstar_eq_image]
  apply IsCompact.image _ continuous_evalPtStar
  -- the corresponding subset of `ℝ⁵` is compact
  have hB : IsCompact {p : Fin 5 → ℝ | KboxProp p} := by
    apply Metric.isCompact_of_isClosed_isBounded
    · have : {p : Fin 5 → ℝ | KboxProp p} =
          {p | p 1 ^ 2 + p 2 ^ 2 = 1} ∩ {p | p 3 = p 1} ∩ {p | p 4 = p 2} ∩ {p | 0 ≤ p 0} ∩
            {p | p 0 * (2 * p 1 + p 0) = 0} := by
        ext p; simp [KboxProp, and_assoc]
      rw [this]
      refine ((((isClosed_eq ?_ ?_).inter (isClosed_eq ?_ ?_)).inter (isClosed_eq ?_ ?_)).inter
        (isClosed_le ?_ ?_)).inter (isClosed_eq ?_ ?_) <;> fun_prop
    · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨2, fun p hp => ?_⟩
      obtain ⟨h1, h3, h4, h0, ht⟩ := hp
      have hu : |p 1| ≤ 1 := by
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg (p 1), sq_nonneg (p 2)]
      have hv : |p 2| ≤ 1 := by
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg (p 1), sq_nonneg (p 2)]
      have htb : |p 0| ≤ 2 := by
        rcases mul_eq_zero.1 ht with h | h
        · rw [h]; norm_num
        · rw [abs_of_nonneg h0]; nlinarith [abs_le.1 hu]
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
      intro i
      rw [Real.norm_eq_abs]
      fin_cases i
      · exact htb
      · exact hu.trans (by norm_num)
      · exact hv.trans (by norm_num)
      · show |p 3| ≤ 2; rw [h3]; exact hu.trans (by norm_num)
      · show |p 4| ≤ 2; rw [h4]; exact hv.trans (by norm_num)
  have hcl : IsClosed {p : Fin 5 → ℝ | p 3 * p 1 + p 4 * p 2 = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  exact hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hB

@[simp] lemma v5_0 (a₀ a₁ a₂ a₃ a₄ : ℝ) : (![a₀, a₁, a₂, a₃, a₄] : Fin 5 → ℝ) 0 = a₀ := rfl
@[simp] lemma v5_1 (a₀ a₁ a₂ a₃ a₄ : ℝ) : (![a₀, a₁, a₂, a₃, a₄] : Fin 5 → ℝ) 1 = a₁ := rfl
@[simp] lemma v5_2 (a₀ a₁ a₂ a₃ a₄ : ℝ) : (![a₀, a₁, a₂, a₃, a₄] : Fin 5 → ℝ) 2 = a₂ := rfl
@[simp] lemma v5_3 (a₀ a₁ a₂ a₃ a₄ : ℝ) : (![a₀, a₁, a₂, a₃, a₄] : Fin 5 → ℝ) 3 = a₃ := rfl
@[simp] lemma v5_4 (a₀ a₁ a₂ a₃ a₄ : ℝ) : (![a₀, a₁, a₂, a₃, a₄] : Fin 5 → ℝ) 4 = a₄ := rfl

/-! ### The map `K* → K₀` -/

lemma comap_phi_x (z : RealPt Astar) :
    RealPt.comap (phi : A₀ →+* Astar) z x = 1 + coords z 0 * coords z 1 := by
  simp [RealPt.comap_apply, coords]

lemma comap_phi_y (z : RealPt Astar) :
    RealPt.comap (phi : A₀ →+* Astar) z y = coords z 0 * coords z 2 := by
  simp [RealPt.comap_apply, coords]

lemma mapsTo_Kstar : MapsTo (RealPt.comap (phi : A₀ →+* Astar)) Kstar K₀ := by
  intro z hz
  obtain ⟨h1, -, -, -, ht⟩ := hz
  show RealPt.comap (phi : A₀ →+* Astar) z Δ = 0
  rw [Δ_eval, comap_phi_x, comap_phi_y]
  linear_combination ht + (coords z 0) ^ 2 * h1

/-- The point `(t, u, v, r, s) = (0, 1, 0, 1, 0)` of `K*` over `(1, 0)`. -/
def pt₁₀ : Ksub := ⟨![0, 1, 0, 1, 0], by simp⟩

/-- The point of `K*` over `(a, b) ∈ K₀ \ {(1, 0)}`:
`t = √((a-1)² + b²)`, `u = r = (a-1)/t`, `v = s = b/t`. -/
def ptOver (a b : ℝ) (h : 0 < (a - 1) ^ 2 + b ^ 2) : Ksub :=
  ⟨![√((a - 1) ^ 2 + b ^ 2), (a - 1) / √((a - 1) ^ 2 + b ^ 2), b / √((a - 1) ^ 2 + b ^ 2),
      (a - 1) / √((a - 1) ^ 2 + b ^ 2), b / √((a - 1) ^ 2 + b ^ 2)], by
    have hτ := Real.sqrt_pos.2 h
    have hτ2 := Real.sq_sqrt h.le
    simp only [v5_1, v5_2, v5_3, v5_4]
    field_simp
    linarith⟩

lemma ptOver_mem (a b : ℝ) (hab : 0 < (a - 1) ^ 2 + b ^ 2) (hc : a ^ 2 + b ^ 2 = 1) :
    KboxProp (ptOver a b hab).1 := by
  have hτ := Real.sqrt_pos.2 hab
  have hτ2 := Real.sq_sqrt hab.le
  refine ⟨?_, rfl, rfl, hτ.le, ?_⟩
  · simp only [ptOver, v5_1, v5_2]
    field_simp; linarith
  · simp only [ptOver, v5_0, v5_1]
    field_simp
    nlinarith

lemma coords_eq_of_mem_fiber {z : RealPt Astar} (hz : z ∈ Kstar) {a b : ℝ}
    (hx : RealPt.comap (phi : A₀ →+* Astar) z x = a)
    (hy : RealPt.comap (phi : A₀ →+* Astar) z y = b)
    (hab : 0 < (a - 1) ^ 2 + b ^ 2) : coords z = (ptOver a b hab).1 := by
  obtain ⟨h1, h3, h4, h0, ht⟩ := hz
  rw [comap_phi_x] at hx
  rw [comap_phi_y] at hy
  set c := coords z
  have hc0 : c 0 ≠ 0 := by
    intro h
    rw [h] at hx hy
    have ha : a = 1 := by linarith
    have hb : b = 0 := by linarith
    rw [ha, hb] at hab
    norm_num at hab
  have hsq : c 0 ^ 2 = (a - 1) ^ 2 + b ^ 2 := by
    rw [← hx, ← hy]; linear_combination (-(c 0) ^ 2) * h1
  have hτ : √((a - 1) ^ 2 + b ^ 2) = c 0 := by
    rw [← hsq, Real.sqrt_sq h0]
  funext i
  fin_cases i
  · show c 0 = (ptOver a b hab).1 0
    simp only [ptOver, v5_0, hτ]
  · show c 1 = (ptOver a b hab).1 1
    simp only [ptOver, v5_1, hτ]
    rw [eq_div_iff hc0]; linarith
  · show c 2 = (ptOver a b hab).1 2
    simp only [ptOver, v5_2, hτ]
    rw [eq_div_iff hc0]; linarith
  · show c 3 = (ptOver a b hab).1 3
    simp only [ptOver, v5_3, hτ]
    rw [eq_div_iff hc0, h3]; linarith
  · show c 4 = (ptOver a b hab).1 4
    simp only [ptOver, v5_4, hτ]
    rw [eq_div_iff hc0, h4]; linarith

lemma comap_evalPtStar_x (p : Ksub) :
    RealPt.comap (phi : A₀ →+* Astar) (evalPtStar p) x = 1 + p.1 0 * p.1 1 := by
  rw [comap_phi_x, coords_evalPtStar]

lemma comap_evalPtStar_y (p : Ksub) :
    RealPt.comap (phi : A₀ →+* Astar) (evalPtStar p) y = p.1 0 * p.1 2 := by
  rw [comap_phi_y, coords_evalPtStar]

/-- The restriction `K* → K₀`. -/
abbrev qStar : Kstar → K₀ := mapsTo_Kstar.restrict _ _ _

lemma circle_of_mem_K₀ (w : RealPt A₀) (hw : w ∈ K₀) : w x ^ 2 + w y ^ 2 = 1 := by
  have : w Δ = 0 := hw
  rw [Δ_eval] at this; linarith

lemma pos_of_ne (w : RealPt A₀) (h10 : ¬(w x = 1 ∧ w y = 0)) : 0 < (w x - 1) ^ 2 + w y ^ 2 := by
  by_contra hle
  push Not at hle
  apply h10
  constructor <;> nlinarith [sq_nonneg (w x - 1), sq_nonneg (w y)]

lemma qStar_surjective : Function.Surjective qStar := by
  rintro ⟨w, hw⟩
  have hc := circle_of_mem_K₀ w hw
  by_cases h10 : w x = 1 ∧ w y = 0
  · refine ⟨⟨evalPtStar pt₁₀, ?_⟩, ?_⟩
    · show KboxProp (coords (evalPtStar pt₁₀))
      rw [coords_evalPtStar]
      refine ⟨by simp [pt₁₀], rfl, rfl, by simp [pt₁₀], by simp [pt₁₀]⟩
    · apply Subtype.ext
      apply realPt_A₀_ext
      · show RealPt.comap _ (evalPtStar pt₁₀) x = w x
        rw [comap_evalPtStar_x, h10.1]; simp [pt₁₀]
      · show RealPt.comap _ (evalPtStar pt₁₀) y = w y
        rw [comap_evalPtStar_y, h10.2]; simp [pt₁₀]
  · have hab := pos_of_ne w h10
    refine ⟨⟨evalPtStar (ptOver (w x) (w y) hab), ?_⟩, ?_⟩
    · show KboxProp (coords (evalPtStar _))
      rw [coords_evalPtStar]
      exact ptOver_mem _ _ hab hc
    · apply Subtype.ext
      have hτ := Real.sqrt_pos.2 hab
      apply realPt_A₀_ext
      · show RealPt.comap _ (evalPtStar _) x = w x
        rw [comap_evalPtStar_x]
        simp only [ptOver, v5_0, v5_1]
        field_simp; ring
      · show RealPt.comap _ (evalPtStar _) y = w y
        rw [comap_evalPtStar_y]
        simp only [ptOver, v5_0, v5_2]
        field_simp

/-- The circle `{t = 0, u² + v² = 1, r = u, s = v}` of `K*` over `(1, 0)`, parametrized by the
angle `θ`: `(t, u, v, r, s) = (0, cos θ, sin θ, cos θ, sin θ)`. -/
def circPt (θ : ℝ) : Ksub :=
  ⟨![0, Real.cos θ, Real.sin θ, Real.cos θ, Real.sin θ], by
    simp only [v5_1, v5_2, v5_3, v5_4]; nlinarith [Real.sin_sq_add_cos_sq θ]⟩

lemma circPt_mem (θ : ℝ) : evalPtStar (circPt θ) ∈ Kstar := by
  show KboxProp (coords (evalPtStar (circPt θ)))
  rw [coords_evalPtStar]
  refine ⟨?_, rfl, rfl, le_rfl, by simp [circPt]⟩
  simp only [circPt, v5_1, v5_2]
  nlinarith [Real.sin_sq_add_cos_sq θ]

lemma continuous_circPt : Continuous circPt := by
  apply Continuous.subtype_mk
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_const
  · exact Real.continuous_cos
  · exact Real.continuous_sin
  · exact Real.continuous_cos
  · exact Real.continuous_sin

lemma qStar_fiber_nonempty (w : RealPt A₀) (hw : w ∈ K₀) :
    (qStar ⁻¹' {⟨w, hw⟩}).Nonempty := by
  obtain ⟨z, hz⟩ := qStar_surjective ⟨w, hw⟩
  exact ⟨z, hz⟩

lemma mem_qStar_fiber {w : RealPt A₀} {hw : w ∈ K₀} {z : RealPt Astar} {hz : z ∈ Kstar} :
    (⟨z, hz⟩ : Kstar) ∈ qStar ⁻¹' {⟨w, hw⟩} ↔ RealPt.comap (phi : A₀ →+* Astar) z = w := by
  simp only [mem_preimage, mem_singleton_iff]
  constructor
  · intro h; exact congrArg Subtype.val h
  · intro h; exact Subtype.ext h

lemma coords_zero_of_fiber_one_zero {z : RealPt Astar} (hz : z ∈ Kstar)
    (hx : RealPt.comap (phi : A₀ →+* Astar) z x = 1)
    (hy : RealPt.comap (phi : A₀ →+* Astar) z y = 0) : coords z 0 = 0 := by
  rw [comap_phi_x] at hx
  rw [comap_phi_y] at hy
  obtain ⟨h1, -, -, -, -⟩ := hz
  have hx' : coords z 0 * coords z 1 = 0 := by linarith
  have : coords z 0 ^ 2 = 0 := by
    linear_combination (-(coords z 0) ^ 2) * h1 + (coords z 0 * coords z 1) * hx' +
      (coords z 0 * coords z 2) * hy
  exact pow_eq_zero_iff (by norm_num) |>.1 this

/-- Every point of the unit circle is `(cos θ, sin θ)`. -/
lemma exists_angle {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) : ∃ θ : ℝ, Real.cos θ = a ∧ Real.sin θ = b := by
  set w : ℂ := ⟨a, b⟩
  have hw : ‖w‖ = 1 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp [w, h]
  have hw0 : w ≠ 0 := by intro h0; rw [h0, norm_zero] at hw; exact zero_ne_one hw
  exact ⟨w.arg, by rw [Complex.cos_arg hw0, hw, div_one], by rw [Complex.sin_arg, hw, div_one]⟩

lemma coords_circPt_eq {z : RealPt Astar} (hz : z ∈ Kstar) (h0 : coords z 0 = 0) {θ : ℝ}
    (hc : Real.cos θ = coords z 1) (hs : Real.sin θ = coords z 2) :
    (circPt θ).1 = coords z := by
  obtain ⟨-, h3, h4, -, -⟩ := hz
  funext i
  fin_cases i
  · show (0 : ℝ) = coords z 0
    rw [h0]
  · exact hc
  · exact hs
  · show Real.cos θ = coords z 3
    rw [h3, hc]
  · show Real.sin θ = coords z 4
    rw [h4, hs]

lemma fiber_one_zero (w : RealPt A₀) (hw : w ∈ K₀) (h10 : w x = 1 ∧ w y = 0) :
    qStar ⁻¹' {⟨w, hw⟩} =
      range (fun θ : ℝ => (⟨evalPtStar (circPt θ), circPt_mem θ⟩ : Kstar)) := by
  ext ⟨z, hz⟩
  rw [mem_qStar_fiber, mem_range]
  constructor
  · intro hzw
    have hx := congrArg (fun φ : RealPt A₀ => φ x) hzw
    have hy := congrArg (fun φ : RealPt A₀ => φ y) hzw
    simp only [h10.1, h10.2] at hx hy
    have h0 := coords_zero_of_fiber_one_zero hz hx hy
    obtain ⟨θ, hc, hs⟩ := exists_angle hz.1
    refine ⟨θ, Subtype.ext (realPt_Astar_ext ?_)⟩
    rw [coords_evalPtStar]
    exact coords_circPt_eq hz h0 hc hs
  · rintro ⟨θ, hθ⟩
    have hzθ : z = evalPtStar (circPt θ) := (congrArg Subtype.val hθ).symm
    subst hzθ
    apply realPt_A₀_ext
    · rw [comap_evalPtStar_x, h10.1]; simp [circPt]
    · rw [comap_evalPtStar_y, h10.2]; simp [circPt]

lemma fiber_subsingleton (w : RealPt A₀) (hw : w ∈ K₀) (h10 : ¬(w x = 1 ∧ w y = 0)) :
    (qStar ⁻¹' {⟨w, hw⟩}).Subsingleton := by
  have hab := pos_of_ne w h10
  rintro ⟨z₁, hz₁⟩ h₁ ⟨z₂, hz₂⟩ h₂
  rw [mem_qStar_fiber] at h₁ h₂
  apply Subtype.ext
  apply realPt_Astar_ext
  rw [coords_eq_of_mem_fiber hz₁ (congrArg (fun φ : RealPt A₀ => φ x) h₁)
      (congrArg (fun φ : RealPt A₀ => φ y) h₁) hab,
    coords_eq_of_mem_fiber hz₂ (congrArg (fun φ : RealPt A₀ => φ x) h₂)
      (congrArg (fun φ : RealPt A₀ => φ y) h₂) hab]

/-- **`K* → K₀` is a monotone surjection**: the fibre over `(1, 0)` is a circle, and all other
fibres are points. -/
theorem isMonotoneSurjOn_Kstar :
    IsMonotoneSurjOn (RealPt.comap (phi : A₀ →+* Astar)) Kstar K₀ := by
  refine ⟨mapsTo_Kstar, ⟨?_, qStar_surjective, ?_⟩⟩
  · exact ((RealPt.continuous_comap _).comp continuous_subtype_val).subtype_mk _
  rintro ⟨w, hw⟩
  by_cases h10 : w x = 1 ∧ w y = 0
  · rw [fiber_one_zero w hw h10]
    exact isConnected_range ((continuous_evalPtStar.comp continuous_circPt).subtype_mk _)
  · exact ⟨qStar_fiber_nonempty w hw, (fiber_subsingleton w hw h10).isPreconnected⟩

/-- **The pullback of the Möbius bundle `L₀` to `K*` is nonorientable** (Lemma 2.1). -/
theorem Kstar_nonorientable :
    ¬ LineFieldOrientable (fun z : Kstar => z.1 ((phi : A₀ →+* Astar) x))
      (fun z : Kstar => z.1 ((phi : A₀ →+* Astar) y)) := by
  have := @nonorientable_pullback A₀ Astar _ _ (phi : A₀ →+* Astar) x y K₀ Kstar
  exact this isCompact_Kstar isMonotoneSurjOn_Kstar (fun w hw => circle_of_mem_K₀ w hw)
    L₀_nonorientable

/-- **Proposition 4.6 holds for `A = ℚ[x,y]`, `I = (x - 1, y)`, `K = K₀`** (Section 6.3),
unconditionally: `A' = A*` is a smooth finitely generated factorial `ℚ`-domain, `ℚ[x,y] → A*` is
injective, `(x - 1, y) A* = t A*` is principal, and `K* → K₀` is a monotone surjection. -/
theorem principalizationExtension_example :
    ∃ (A' : SmoothFactorialDomain) (f : A₀SFD →ₐ[ℚ] A') (K' : Set (RealPt A')),
      Function.Injective f ∧ ((Ideal.span {x - 1, y} : Ideal A₀SFD).map f).IsPrincipal ∧
        IsCompact K' ∧ IsMonotoneSurjOn (RealPt.comap (f : A₀SFD →+* A')) K' K₀ :=
  ⟨AstarSFD, phi, Kstar, phi_injective, ⟨⟨t, map_span_eq⟩⟩, isCompact_Kstar,
    isMonotoneSurjOn_Kstar⟩

end BezoutCounterexample.Explicit
