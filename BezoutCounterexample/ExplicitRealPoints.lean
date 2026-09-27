import BezoutCounterexample.Explicit
import BezoutCounterexample.Mobius

/-!
# Section 6.3: an explicit principalization extension (real points)

This file completes Section 6.3 of the paper (the algebra is in `Explicit.lean`). Using the
coordinates `(t, u, v, r₀, r₁)` on `Spec(A*)(ℝ)` (`coords`; a real point is determined by them,
`realPt_ext`, and every point of `ℝ⁵` with `r₀ u + r₁ v = 1` is a real point, `ptOf`), define

  `K* = {u² + v² = 1, r₀ = u, r₁ = v, t ≥ 0, t(2u + t) = 0} ⊆ Spec(A*)(ℝ)` (`Kstar`).

* `isCompact_Kstar`: `K*` is closed and bounded (`|u|, |v|, |r₀|, |r₁| ≤ 1`, and `t = 0` or
  `t = -2u`, so `0 ≤ t ≤ 2`), hence compact (`RealPt.isCompact_iff`).
* `mapsTo_Kstar`: `(t, u, v, r₀, r₁) ↦ (1 + t u, t v)` sends `K*` into `K₀`, because the pullback
  of `Δ` is `2tu + t²(u² + v²) = t(2u + t) = 0`.
* `fiber_subsingleton`, `ptOver`: over `(a, b) ∈ K₀ \ {(1, 0)}` the unique inverse image is
  `t = √((a - 1)² + b²)`, `u = r₀ = (a - 1)/t`, `v = r₁ = b/t`.
* `fiber_one_zero`: the fibre over `(1, 0)` is the circle `t = 0, u² + v² = 1, r₀ = u, r₁ = v`.
* `isMonotoneSurjOn_Kstar`: hence `K* → K₀` is a monotone surjection, and
  `Kstar_nonorientable`: the pullback of `L₀` to `K*` is nonorientable (Lemma 2.1).
* `principalization_extension_example` collects the conclusion of Proposition 4.6 for
  `A = ℚ[x, y]`, `I = (x - 1, y)` and `K = K₀`, with `A' = A*` (`AstarSFD`) and `K' = K*`.
-/

noncomputable section

namespace BezoutCounterexample.Explicit

open Set Topology MvPolynomial

/-! ## Coordinates on `Spec(A*)(ℝ)` -/

/-- The generators `(t, u, v, r₀, r₁)` of `A*`. -/
def gens : Fin 5 → Astar := fun i => mk (X i)

/-- The coordinates `(t, u, v, r₀, r₁)` of a real point of `A*`. -/
abbrev coords (z : RealPt Astar) : Fin 5 → ℝ := RealPt.evalGens gens z

lemma coords_zero (z : RealPt Astar) : coords z 0 = z t := rfl
lemma coords_one (z : RealPt Astar) : coords z 1 = z u := rfl
lemma coords_two (z : RealPt Astar) : coords z 2 = z v := rfl
lemma coords_three (z : RealPt Astar) : coords z 3 = z r₀ := rfl
lemma coords_four (z : RealPt Astar) : coords z 4 = z r₁ := rfl

/-- The relation `r₀ u + r₁ v = 1` holds at every real point. -/
lemma coords_rel (z : RealPt Astar) : coords z 3 * coords z 1 + coords z 4 * coords z 2 = 1 := by
  have h := congrArg z rel_eq_one
  simp only [map_add, map_mul, map_one] at h
  exact h

/-- A real point of `A*` is determined by its coordinates. -/
lemma realPt_ext {z w : RealPt Astar} (h : coords z = coords w) : z = w :=
  RealPt.evalGens_injective adjoin_gens h

/-- The coordinates form a topological embedding of `Spec(A*)(ℝ)` into `ℝ⁵`. -/
lemma isEmbedding_coords : IsEmbedding coords := RealPt.isEmbedding_evalGens adjoin_gens

@[simp] lemma v5_0 (a₀ a₁ a₂ a₃ a₄ : ℝ) : (![a₀, a₁, a₂, a₃, a₄] : Fin 5 → ℝ) 0 = a₀ := rfl
@[simp] lemma v5_1 (a₀ a₁ a₂ a₃ a₄ : ℝ) : (![a₀, a₁, a₂, a₃, a₄] : Fin 5 → ℝ) 1 = a₁ := rfl
@[simp] lemma v5_2 (a₀ a₁ a₂ a₃ a₄ : ℝ) : (![a₀, a₁, a₂, a₃, a₄] : Fin 5 → ℝ) 2 = a₂ := rfl
@[simp] lemma v5_3 (a₀ a₁ a₂ a₃ a₄ : ℝ) : (![a₀, a₁, a₂, a₃, a₄] : Fin 5 → ℝ) 3 = a₃ := rfl
@[simp] lemma v5_4 (a₀ a₁ a₂ a₃ a₄ : ℝ) : (![a₀, a₁, a₂, a₃, a₄] : Fin 5 → ℝ) 4 = a₄ := rfl

/-- The real point of `A*` with coordinates `p = (t, u, v, r₀, r₁)`, where `r₀ u + r₁ v = 1`. -/
def ptOf (p : Fin 5 → ℝ) (hp : p 3 * p 1 + p 4 * p 2 = 1) : RealPt Astar :=
  RealPt.ofHom (lift p hp).toRingHom

@[simp] lemma coords_ptOf (p : Fin 5 → ℝ) (hp : p 3 * p 1 + p 4 * p 2 = 1) :
    coords (ptOf p hp) = p := by
  funext i
  exact MvPolynomial.aeval_X p i

/-- Continuity of families of real points given by continuous coordinates. -/
lemma continuous_ptOf {Y : Type*} [TopologicalSpace Y] {g : Y → Fin 5 → ℝ} (hg : Continuous g)
    (hrel : ∀ y, g y 3 * g y 1 + g y 4 * g y 2 = 1) :
    Continuous fun y => ptOf (g y) (hrel y) := by
  rw [isEmbedding_coords.continuous_iff]
  convert hg using 1
  funext y
  exact coords_ptOf _ _

/-! ## The compact set `K*` -/

/-- The conditions defining `K*`, in the coordinates `(t, u, v, r₀, r₁)`. -/
def KstarCond (p : Fin 5 → ℝ) : Prop :=
  p 1 ^ 2 + p 2 ^ 2 = 1 ∧ p 3 = p 1 ∧ p 4 = p 2 ∧ 0 ≤ p 0 ∧ p 0 * (2 * p 1 + p 0) = 0

/-- **`K* = {u² + v² = 1, r₀ = u, r₁ = v, t ≥ 0, t(2u + t) = 0} ⊆ Spec(A*)(ℝ)`.** -/
def Kstar : Set (RealPt Astar) := {z | KstarCond (coords z)}

/-- **`K*` is compact**: it is closed, and `|u|, |v|, |r₀|, |r₁| ≤ 1`, while `t = 0` or `t = -2u`,
so `0 ≤ t ≤ 2`. -/
theorem isCompact_Kstar : IsCompact Kstar := by
  rw [RealPt.isCompact_iff adjoin_gens]
  refine ⟨?_, fun i => ⟨2, fun z hz => ?_⟩⟩
  · -- closed
    have hc := RealPt.continuous_evalGens gens
    have : Kstar = coords ⁻¹' {p | p 1 ^ 2 + p 2 ^ 2 = 1} ∩ coords ⁻¹' {p | p 3 = p 1} ∩
        coords ⁻¹' {p | p 4 = p 2} ∩ coords ⁻¹' {p | 0 ≤ p 0} ∩
        coords ⁻¹' {p | p 0 * (2 * p 1 + p 0) = 0} := by
      ext z; simp [Kstar, KstarCond, and_assoc]
    rw [this]
    refine ((((IsClosed.preimage hc ?_).inter (IsClosed.preimage hc ?_)).inter
      (IsClosed.preimage hc ?_)).inter (IsClosed.preimage hc ?_)).inter (IsClosed.preimage hc ?_)
    · exact isClosed_eq (by fun_prop) continuous_const
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · exact isClosed_le continuous_const (by fun_prop)
    · exact isClosed_eq (by fun_prop) continuous_const
  · -- bounded
    obtain ⟨h1, h3, h4, h0, ht⟩ := hz
    have hu : |coords z 1| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (coords z 1), sq_nonneg (coords z 2)]
    have hv : |coords z 2| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (coords z 1), sq_nonneg (coords z 2)]
    have htb : |coords z 0| ≤ 2 := by
      rcases mul_eq_zero.1 ht with h | h
      · rw [h]; norm_num
      · rw [abs_of_nonneg h0]; nlinarith [abs_le.1 hu]
    change |coords z i| ≤ 2
    fin_cases i
    · exact htb
    · exact hu.trans (by norm_num)
    · exact hv.trans (by norm_num)
    · change |coords z 3| ≤ 2; rw [h3]; exact hu.trans (by norm_num)
    · change |coords z 4| ≤ 2; rw [h4]; exact hv.trans (by norm_num)

/-! ## The map `K* → K₀` -/

lemma comap_φ_x (z : RealPt Astar) :
    RealPt.comap (φ : A₀ →+* Astar) z x = 1 + coords z 0 * coords z 1 := by
  rw [coords_zero, coords_one]
  simp [RealPt.comap_apply]

lemma comap_φ_y (z : RealPt Astar) :
    RealPt.comap (φ : A₀ →+* Astar) z y = coords z 0 * coords z 2 := by
  rw [coords_zero, coords_two]
  simp [RealPt.comap_apply]

/-- `K*` maps into `K₀`: the pullback of `Δ` is `2tu + t²(u² + v²) = t(2u + t) = 0`. -/
theorem mapsTo_Kstar : MapsTo (RealPt.comap (φ : A₀ →+* Astar)) Kstar K₀ := by
  intro z hz
  obtain ⟨h1, -, -, -, ht⟩ := hz
  show RealPt.comap (φ : A₀ →+* Astar) z Δ = 0
  rw [Δ_eval, comap_φ_x, comap_φ_y]
  linear_combination ht + (coords z 0) ^ 2 * h1

/-- The restriction `K* → K₀`. -/
abbrev qStar : Kstar → K₀ := mapsTo_Kstar.restrict _ _ _

/-- The point `(t, u, v, r₀, r₁) = (0, 1, 0, 1, 0)` of `K*`, over `(1, 0)`. -/
def pt₁₀ : RealPt Astar := ptOf ![0, 1, 0, 1, 0] (by simp)

/-- The point of `K*` over `(a, b) ∈ K₀ \ {(1, 0)}`: `t = √((a - 1)² + b²)`, `u = r₀ = (a - 1)/t`,
`v = r₁ = b/t`. -/
def ptOver (a b : ℝ) (h : 0 < (a - 1) ^ 2 + b ^ 2) : RealPt Astar :=
  ptOf ![√((a - 1) ^ 2 + b ^ 2), (a - 1) / √((a - 1) ^ 2 + b ^ 2), b / √((a - 1) ^ 2 + b ^ 2),
      (a - 1) / √((a - 1) ^ 2 + b ^ 2), b / √((a - 1) ^ 2 + b ^ 2)] (by
    have hτ := Real.sqrt_pos.2 h
    have hτ2 := Real.sq_sqrt h.le
    simp only [v5_1, v5_2, v5_3, v5_4]
    field_simp
    linarith)

/-- The point `ptOver a b` lies in `K*`; here `t > 0`, and `2u + t = 0` follows from
`a² + b² = 1`. -/
lemma ptOver_mem (a b : ℝ) (hab : 0 < (a - 1) ^ 2 + b ^ 2) (hc : a ^ 2 + b ^ 2 = 1) :
    ptOver a b hab ∈ Kstar := by
  have hτ := Real.sqrt_pos.2 hab
  have hτ2 := Real.sq_sqrt hab.le
  show KstarCond (coords (ptOf _ _))
  rw [coords_ptOf]
  refine ⟨?_, rfl, rfl, hτ.le, ?_⟩
  · simp only [v5_1, v5_2]
    field_simp; linarith
  · simp only [v5_0, v5_1]
    field_simp
    nlinarith

lemma coords_eq_of_mem_fiber {z : RealPt Astar} (hz : z ∈ Kstar) {a b : ℝ}
    (hx : RealPt.comap (φ : A₀ →+* Astar) z x = a)
    (hy : RealPt.comap (φ : A₀ →+* Astar) z y = b)
    (hab : 0 < (a - 1) ^ 2 + b ^ 2) : coords z = coords (ptOver a b hab) := by
  obtain ⟨h1, h3, h4, h0, ht⟩ := hz
  rw [comap_φ_x] at hx
  rw [comap_φ_y] at hy
  rw [ptOver, coords_ptOf]
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
  · show c 0 = _
    simp only [Fin.zero_eta, v5_0, hτ]
  · show c 1 = _
    simp only [Fin.mk_one, v5_1, hτ]
    rw [eq_div_iff hc0]; linarith
  · show c 2 = _
    simp only [Fin.reduceFinMk, v5_2, hτ]
    rw [eq_div_iff hc0]; linarith
  · show c 3 = _
    simp only [Fin.reduceFinMk, v5_3, hτ]
    rw [eq_div_iff hc0, h3]; linarith
  · show c 4 = _
    simp only [Fin.reduceFinMk, v5_4, hτ]
    rw [eq_div_iff hc0, h4]; linarith

lemma pos_of_ne (w : RealPt A₀) (h10 : ¬(w x = 1 ∧ w y = 0)) : 0 < (w x - 1) ^ 2 + w y ^ 2 := by
  by_contra hle
  push Not at hle
  apply h10
  constructor <;> nlinarith [sq_nonneg (w x - 1), sq_nonneg (w y)]

/-- `K* → K₀` is surjective. -/
lemma qStar_surjective : Function.Surjective qStar := by
  rintro ⟨w, hw⟩
  have hc := K₀_circle hw
  by_cases h10 : w x = 1 ∧ w y = 0
  · refine ⟨⟨pt₁₀, ?_⟩, ?_⟩
    · show KstarCond (coords (ptOf _ _))
      rw [coords_ptOf]
      refine ⟨by simp, rfl, rfl, by simp, by simp⟩
    · apply Subtype.ext
      apply realPt_A₀_ext
      · show RealPt.comap _ pt₁₀ x = w x
        rw [comap_φ_x, pt₁₀, coords_ptOf, h10.1]; simp
      · show RealPt.comap _ pt₁₀ y = w y
        rw [comap_φ_y, pt₁₀, coords_ptOf, h10.2]; simp
  · have hab := pos_of_ne w h10
    refine ⟨⟨ptOver (w x) (w y) hab, ptOver_mem _ _ hab hc⟩, ?_⟩
    apply Subtype.ext
    have hτ := Real.sqrt_pos.2 hab
    apply realPt_A₀_ext
    · show RealPt.comap _ (ptOver (w x) (w y) hab) x = w x
      rw [comap_φ_x, ptOver, coords_ptOf]
      simp only [v5_0, v5_1]
      field_simp; ring
    · show RealPt.comap _ (ptOver (w x) (w y) hab) y = w y
      rw [comap_φ_y, ptOver, coords_ptOf]
      simp only [v5_0, v5_2]
      field_simp

/-- The circle of `K*` over `(1, 0)`, parametrized by the angle `θ`:
`(t, u, v, r₀, r₁) = (0, cos θ, sin θ, cos θ, sin θ)`. -/
def circPt (θ : ℝ) : RealPt Astar :=
  ptOf ![0, Real.cos θ, Real.sin θ, Real.cos θ, Real.sin θ] (by
    simp only [v5_1, v5_2, v5_3, v5_4]; nlinarith [Real.sin_sq_add_cos_sq θ])

lemma coords_circPt (θ : ℝ) :
    coords (circPt θ) = ![0, Real.cos θ, Real.sin θ, Real.cos θ, Real.sin θ] :=
  coords_ptOf _ _

lemma circPt_mem (θ : ℝ) : circPt θ ∈ Kstar := by
  show KstarCond (coords (ptOf _ _))
  rw [coords_ptOf]
  refine ⟨?_, rfl, rfl, le_rfl, by simp⟩
  simp only [v5_1, v5_2]
  nlinarith [Real.sin_sq_add_cos_sq θ]

lemma continuous_circPt : Continuous circPt := by
  apply continuous_ptOf
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_const
  · exact Real.continuous_cos
  · exact Real.continuous_sin
  · exact Real.continuous_cos
  · exact Real.continuous_sin

lemma mem_qStar_fiber {w : RealPt A₀} {hw : w ∈ K₀} {z : RealPt Astar} {hz : z ∈ Kstar} :
    (⟨z, hz⟩ : Kstar) ∈ qStar ⁻¹' {⟨w, hw⟩} ↔ RealPt.comap (φ : A₀ →+* Astar) z = w := by
  simp only [mem_preimage, mem_singleton_iff]
  constructor
  · intro h; exact congrArg Subtype.val h
  · intro h; exact Subtype.ext h

lemma coords_zero_of_fiber_one_zero {z : RealPt Astar} (hz : z ∈ Kstar)
    (hx : RealPt.comap (φ : A₀ →+* Astar) z x = 1)
    (hy : RealPt.comap (φ : A₀ →+* Astar) z y = 0) : coords z 0 = 0 := by
  rw [comap_φ_x] at hx
  rw [comap_φ_y] at hy
  obtain ⟨h1, -, -, -, -⟩ := hz
  have hx' : coords z 0 * coords z 1 = 0 := by linarith
  have : coords z 0 ^ 2 = 0 := by
    linear_combination (-(coords z 0) ^ 2) * h1 + (coords z 0 * coords z 1) * hx' +
      (coords z 0 * coords z 2) * hy
  exact pow_eq_zero_iff (by norm_num) |>.1 this

/-- Every point of the unit circle is `(cos θ, sin θ)`. -/
lemma exists_angle {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = a ∧ Real.sin θ = b := by
  set w : ℂ := ⟨a, b⟩
  have hw : ‖w‖ = 1 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp [w, h]
  have hw0 : w ≠ 0 := by intro h0; rw [h0, norm_zero] at hw; exact zero_ne_one hw
  exact ⟨w.arg, by rw [Complex.cos_arg hw0, hw, div_one], by rw [Complex.sin_arg, hw, div_one]⟩

/-- **The fibre of `K* → K₀` over `(1, 0)` is the circle** `t = 0, u² + v² = 1, r₀ = u, r₁ = v`. -/
lemma fiber_one_zero (w : RealPt A₀) (hw : w ∈ K₀) (h10 : w x = 1 ∧ w y = 0) :
    qStar ⁻¹' {⟨w, hw⟩} = range (fun θ : ℝ => (⟨circPt θ, circPt_mem θ⟩ : Kstar)) := by
  ext ⟨z, hz⟩
  rw [mem_qStar_fiber, mem_range]
  constructor
  · intro hzw
    have hx := congrArg (fun ζ : RealPt A₀ => ζ x) hzw
    have hy := congrArg (fun ζ : RealPt A₀ => ζ y) hzw
    simp only [h10.1, h10.2] at hx hy
    have h0 := coords_zero_of_fiber_one_zero hz hx hy
    obtain ⟨θ, hc, hs⟩ := exists_angle hz.1
    refine ⟨θ, Subtype.ext (realPt_ext ?_)⟩
    obtain ⟨-, h3, h4, -, -⟩ := hz
    show coords (circPt θ) = coords z
    rw [coords_circPt]
    funext i
    fin_cases i
    · exact h0.symm
    · exact hc
    · exact hs
    · show Real.cos θ = coords z 3; rw [h3, hc]
    · show Real.sin θ = coords z 4; rw [h4, hs]
  · rintro ⟨θ, hθ⟩
    have hzθ : z = circPt θ := (congrArg Subtype.val hθ).symm
    subst hzθ
    apply realPt_A₀_ext
    · rw [comap_φ_x, coords_circPt, h10.1]; simp
    · rw [comap_φ_y, coords_circPt, h10.2]; simp

/-- **Over `(a, b) ∈ K₀ \ {(1, 0)}` the inverse image is unique.** -/
lemma fiber_subsingleton (w : RealPt A₀) (hw : w ∈ K₀) (h10 : ¬(w x = 1 ∧ w y = 0)) :
    (qStar ⁻¹' {⟨w, hw⟩}).Subsingleton := by
  have hab := pos_of_ne w h10
  rintro ⟨z₁, hz₁⟩ h₁ ⟨z₂, hz₂⟩ h₂
  rw [mem_qStar_fiber] at h₁ h₂
  apply Subtype.ext
  apply realPt_ext
  rw [coords_eq_of_mem_fiber hz₁ (congrArg (fun ζ : RealPt A₀ => ζ x) h₁)
      (congrArg (fun ζ : RealPt A₀ => ζ y) h₁) hab,
    coords_eq_of_mem_fiber hz₂ (congrArg (fun ζ : RealPt A₀ => ζ x) h₂)
      (congrArg (fun ζ : RealPt A₀ => ζ y) h₂) hab]

/-- **`K* → K₀` is a monotone surjection**: the fibre over `(1, 0)` is a circle, and all other
fibres are points. -/
theorem isMonotoneSurjOn_Kstar :
    IsMonotoneSurjOn (RealPt.comap (φ : A₀ →+* Astar)) Kstar K₀ := by
  refine ⟨mapsTo_Kstar, ⟨?_, qStar_surjective, ?_⟩⟩
  · exact ((RealPt.continuous_comap _).comp continuous_subtype_val).subtype_mk _
  rintro ⟨w, hw⟩
  by_cases h10 : w x = 1 ∧ w y = 0
  · rw [fiber_one_zero w hw h10]
    exact isConnected_range (continuous_circPt.subtype_mk _)
  · obtain ⟨z, hz⟩ := qStar_surjective ⟨w, hw⟩
    exact ⟨⟨z, hz⟩, (fiber_subsingleton w hw h10).isPreconnected⟩

/-- **The pullback of `L₀` to `K*` is nonorientable** (Lemma 2.1). -/
theorem Kstar_nonorientable :
    ¬ IsOrientable (fun z : Kstar => z.1 ((φ : A₀ →+* Astar) x))
      (fun z : Kstar => z.1 ((φ : A₀ →+* Astar) y)) :=
  not_isOrientable_pullback (φ : A₀ →+* Astar) x y isCompact_Kstar isMonotoneSurjOn_Kstar
    (fun _ hz => K₀_circle hz) L₀_not_isOrientable

/-- **The explicit principalization extension** (Section 6.3): for `A = ℚ[x, y]`,
`I = (x - 1, y)` and `K = K₀`, the conclusion of Proposition 4.6 holds with the smooth finitely
generated factorial `ℚ`-domain `A' = A*` (`AstarSFD`), the injection `φ : ℚ[x, y] ↪ A*`, and
`K' = K*`: `(x - 1, y) A* = t A*` is principal, `K*` is compact, and `K* → K₀` is a monotone
surjection; consequently the pullback of `L₀` to `K*` is nonorientable. -/
theorem principalization_extension_example :
    Function.Injective φ ∧ ((Ideal.span {x - 1, y} : Ideal A₀).map φ).IsPrincipal ∧
      IsCompact Kstar ∧ IsMonotoneSurjOn (RealPt.comap (φ : A₀ →+* Astar)) Kstar K₀ ∧
      ¬ IsOrientable (fun z : Kstar => z.1 ((φ : A₀ →+* Astar) x))
        (fun z : Kstar => z.1 ((φ : A₀ →+* Astar) y)) :=
  ⟨φ_injective, ⟨⟨t, map_span_eq⟩⟩, isCompact_Kstar, isMonotoneSurjOn_Kstar,
    Kstar_nonorientable⟩

end BezoutCounterexample.Explicit
