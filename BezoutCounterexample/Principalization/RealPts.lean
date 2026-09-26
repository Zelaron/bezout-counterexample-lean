import BezoutCounterexample.Principalization.Induction
import BezoutCounterexample.RealCompact

/-!
# Real points of the torsor and the proof of Proposition 4.6

The compact set `K' ⊆ U(ℝ)` is the weighted sphere bundle
`{w | w ∈ K over A, s ≥ 0, ∑ yₗ^{Eₗ} = 1, σₗ = yₗ^{Eₗ-1}}` with `Eₗ = 2 d!/jₗ`.

* `torsorK_isCompact`: `K'` is compact (closed and bounded on generators).
* Off `V(𝔭)` the fibre is the single point `ptA` (`eq_ptA`).
* Over `V(𝔭)` the fibre is the continuous image `LocPres.Gamma` of `ℝᵏ ∖ {0}`, `k ≥ 2`, via the
  local presentation of the Rees algebra (`LocPres.fib_eq`, `fib_connected`).
* `torsorRealPts`, and hence `principalizationExtension`: **Proposition 4.6**.
-/

noncomputable section


namespace BezoutCounterexample.Principalization

open Jou MvPolynomial

section JPt

variable {R : Type*} [CommRing R] {r : ℕ} (y : Fin r → R)

/-- A real point of `J(y)` from a real point of `R` and values of `σ`. -/
def jPt (z : R →+* ℝ) (sv : Fin r → ℝ) (h : ∑ i, sv i * z (y i) = 1) : RealPt (J y) :=
  RealPt.ofHom (Ideal.Quotient.lift _ (eval₂Hom z sv) (fun a ha => by
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul]
    have : eval₂Hom z sv (rel y) = 0 := by
      simp only [rel, map_sub, map_sum, map_mul, eval₂Hom_X', eval₂Hom_C, map_one]
      rw [sub_eq_zero]
      exact h
    rw [this, mul_zero]))

lemma jPt_mk (z : R →+* ℝ) (sv : Fin r → ℝ) (h) (p : MvPolynomial (Fin r) R) :
    jPt y z sv h (Ideal.Quotient.mk _ p) = eval₂ z sv p := rfl

lemma jPt_algebraMap (z : R →+* ℝ) (sv : Fin r → ℝ) (h) (a : R) :
    jPt y z sv h (algebraMap R (J y) a) = z a := by
  rw [Jou.algebraMap_eq_mk_comp_C, RingHom.comp_apply, jPt_mk, eval₂_C]

lemma jPt_σ (z : R →+* ℝ) (sv : Fin r → ℝ) (h) (i : Fin r) : jPt y z sv h (σ y i) = sv i := by
  show jPt y z sv h (Ideal.Quotient.mk _ (X i)) = _
  rw [jPt_mk, eval₂_X]

/-- Real points of `J(y)` are determined by their restriction to `R` and their values on `σ`. -/
lemma realPt_J_ext {w w' : RealPt (J y)}
    (h1 : ∀ a, w (algebraMap R (J y) a) = w' (algebraMap R (J y) a))
    (h2 : ∀ i, w (σ y i) = w' (σ y i)) : w = w' := by
  ext f
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective f
  induction p using MvPolynomial.induction_on with
  | C a => have := h1 a; rwa [Jou.algebraMap_eq_mk_comp_C] at this
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    exact h2 i

/-- **Continuity in the parameters.** -/
lemma continuous_jPt {X : Type*} [TopologicalSpace X] (z : X → (R →+* ℝ))
    (hz : ∀ a, Continuous fun t => z t a) (sv : X → Fin r → ℝ) (hsv : ∀ i, Continuous fun t => sv t i)
    (h : ∀ t, ∑ i, sv t i * z t (y i) = 1) :
    Continuous fun t => jPt y (z t) (sv t) (h t) := by
  rw [RealPt.continuous_iff]
  intro f
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective f
  simp only [jPt_mk]
  induction p using MvPolynomial.induction_on with
  | C a => simp only [eval₂_C]; exact hz a
  | add p q hp hq => simp only [eval₂_add]; exact hp.add hq
  | mul_X p i hp => simp only [eval₂_mul, eval₂_X]; exact hp.mul (hsv i)

end JPt

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial

section ReesPt

variable {B : Type*} [CommRing B] [Algebra ℚ B] (Φ : WFil B)
  (hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤)

/-- The real point of the Rees algebra given by `z` on `B` and `T ↦ t`. -/
def reesPt (z : B →+* ℝ) (t : ℝˣ) : RealPt (ReesAlg Φ) :=
  RealPt.ofHom ((LaurentPolynomial.eval₂ z t).comp (ReesAlg Φ).val.toRingHom)

lemma reesPt_apply (z : B →+* ℝ) (t : ℝˣ) (p : ReesAlg Φ) :
    reesPt Φ z t p = LaurentPolynomial.eval₂ z t (p : B[T;T⁻¹]) := rfl

lemma reesPt_algebraMap (z : B →+* ℝ) (t : ℝˣ) (b : B) :
    reesPt Φ z t (algebraMap B (ReesAlg Φ) b) = z b := by
  rw [reesPt_apply]
  show LaurentPolynomial.eval₂ z t (algebraMap B B[T;T⁻¹] b) = z b
  rw [← LaurentPolynomial.C_eq_algebraMap, eval₂_C]

lemma reesPt_C_mul_T (z : B →+* ℝ) (t : ℝˣ) {j : ℤ} {g : B} (hg : g ∈ Φ.F j) :
    reesPt Φ z t ⟨LaurentPolynomial.C g * T j, C_mul_T_mem_ReesAlg hg⟩ = z g * ((t ^ j : ℝˣ) : ℝ) := by
  rw [reesPt_apply]
  exact eval₂_C_mul_T _ _ g j

include hneg in
lemma reesPt_s (z : B →+* ℝ) (t : ℝˣ) : reesPt Φ z t (reesS Φ hneg) = ((t⁻¹ : ℝˣ) : ℝ) := by
  rw [reesPt_apply, reesS_coe, eval₂_T]
  simp

include hneg in
/-- **Off the exceptional divisor, a real point is determined by its restriction and `s`.** -/
theorem reesPt_eq (w : RealPt (ReesAlg Φ)) (hw : w (reesS Φ hneg) ≠ 0) :
    w = reesPt Φ ((RealPt.toHom w).comp (algebraMap B (ReesAlg Φ)))
      (Units.mk0 (w (reesS Φ hneg)) hw)⁻¹ := by
  haveI := isLocalization_away_s Φ hneg
  have hu : IsUnit ((RealPt.toHom w) (reesS Φ hneg)) := isUnit_iff_ne_zero.2 hw
  set L : B[T;T⁻¹] →+* ℝ := IsLocalization.Away.lift (reesS Φ hneg) hu
  have hL : ∀ p : ReesAlg Φ, L (p : B[T;T⁻¹]) = w p := fun p =>
    IsLocalization.lift_eq (M := Submonoid.powers (reesS Φ hneg)) _ p
  have hLeq : L = LaurentPolynomial.eval₂ ((RealPt.toHom w).comp (algebraMap B (ReesAlg Φ)))
      (Units.mk0 (w (reesS Φ hneg)) hw)⁻¹ := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial B)) ?_
    refine Polynomial.ringHom_ext (fun b => ?_) ?_
    · simp only [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
        Polynomial.toLaurent_C, eval₂_C]
      rw [LaurentPolynomial.C_eq_algebraMap]
      exact hL (algebraMap B (ReesAlg Φ) b)
    · simp only [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
        Polynomial.toLaurent_X, eval₂_T]
      have h1 : L (T 1) * L (T (-1)) = 1 := by rw [← map_mul, ← T_add]; simp
      have h2 : L (T (-1)) = w (reesS Φ hneg) := hL (reesS Φ hneg)
      rw [h2] at h1
      simp only [zpow_one, Units.val_inv_eq_inv_val, Units.val_mk0]
      exact eq_inv_of_mul_eq_one_left h1
  ext p
  rw [reesPt_apply, ← hLeq, hL]

end ReesPt

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Jou

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)

/-- The natural-number degree of a torsor generator. -/
abbrev gdeg (l : Fin (nGen hI hmax h𝔭 d + 1)) : ℕ := (genDeg hI hmax h𝔭 d l).toNat

/-- The even exponents `2 d! / jₗ` of the weighted sphere. -/
abbrev sphE (l : Fin (nGen hI hmax h𝔭 d + 1)) : ℕ := 2 * (d.factorial / gdeg hI hmax h𝔭 l)

include hd in
lemma gdeg_pos (l) : 0 < gdeg hI hmax h𝔭 (d := d) l := by
  have := genDeg_pos hI hmax h𝔭 d l; simp only [gdeg]; omega

include hd in
lemma gdeg_cast (l) : ((gdeg hI hmax h𝔭 (d := d) l : ℕ) : ℤ) = genDeg hI hmax h𝔭 d l := by
  have := genDeg_pos hI hmax h𝔭 d l; simp only [gdeg]; omega

include hd in
lemma gdeg_mul_sphE (l) : gdeg hI hmax h𝔭 (d := d) l * sphE hI hmax h𝔭 l = 2 * d.factorial := by
  have hle : gdeg hI hmax h𝔭 (d := d) l ≤ d := by
    have := genDeg_le hI hmax h𝔭 d (by omega) l; simp only [gdeg]; omega
  have hdvd : gdeg hI hmax h𝔭 (d := d) l ∣ d.factorial :=
    Nat.dvd_factorial (gdeg_pos hI hmax h𝔭 hd l) hle
  simp only [sphE]
  rw [mul_left_comm, Nat.mul_div_cancel' hdvd]

include hd in
lemma sphE_pos (l) : 0 < sphE hI hmax h𝔭 (d := d) l := by
  have h := gdeg_mul_sphE hI hmax h𝔭 hd l
  rcases Nat.eq_zero_or_pos (sphE hI hmax h𝔭 (d := d) l) with h0 | h0
  · rw [h0, mul_zero] at h; have := Nat.factorial_pos d; omega
  · exact h0

lemma sphE_even (l) : Even (sphE hI hmax h𝔭 (d := d) l) := even_two_mul _

include hd in
/-- `s^{jₗ} yₗ = gₗ` in the Rees algebra. -/
lemma torsorY_mul_s_pow (l : Fin (nGen hI hmax h𝔭 d + 1)) :
    torsorY hI hmax h𝔭 d hπ l *
      reesS (compFil hI hmax h𝔭 d) (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj) ^
        gdeg hI hmax h𝔭 l =
      algebraMap A (ReesAlg (compFil hI hmax h𝔭 d)) (genCoeff hI hmax h𝔭 d π l) := by
  apply Subtype.ext
  show (LaurentPolynomial.C (genCoeff hI hmax h𝔭 d π l) * T (genDeg hI hmax h𝔭 d l)) *
    ((reesS (compFil hI hmax h𝔭 d) (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj) ^
      gdeg hI hmax h𝔭 l : ReesAlg (compFil hI hmax h𝔭 d)) : A[T;T⁻¹]) = algebraMap A A[T;T⁻¹] _
  rw [reesS_pow_coe, gdeg_cast hI hmax h𝔭 hd, mul_assoc, ← T_add, add_neg_cancel, T_zero,
    mul_one, LaurentPolynomial.C_eq_algebraMap]

/-- The image of a torsor generator in `U`. -/
abbrev yU (l : Fin (nGen hI hmax h𝔭 d + 1)) : Torsor hI hmax h𝔭 d hπ :=
  algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ) (torsorY hI hmax h𝔭 d hπ l)

/-- **The compact set of real points on the torsor**: the weighted sphere bundle. -/
def torsorK (K : Set (RealPt A)) : Set (RealPt (Torsor hI hmax h𝔭 d hπ)) :=
  {w | RealPt.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) w ∈ K ∧ 0 ≤ w (torsorS hI hmax h𝔭 hπ) ∧
    ∑ l, w (yU hI hmax h𝔭 hπ l) ^ sphE hI hmax h𝔭 l = 1 ∧
    ∀ l, w (σ (torsorY hI hmax h𝔭 d hπ) l) = w (yU hI hmax h𝔭 hπ l) ^ (sphE hI hmax h𝔭 l - 1)}

include hd in
/-- On the sphere, `s^{2d!} = ∑ gₗ^{Eₗ}`. -/
lemma s_pow_eq (w : RealPt (Torsor hI hmax h𝔭 d hπ))
    (hsph : ∑ l, w (yU hI hmax h𝔭 hπ l) ^ sphE hI hmax h𝔭 l = 1) :
    w (torsorS hI hmax h𝔭 hπ) ^ (2 * d.factorial) =
      ∑ l, w (algebraMap A _ (genCoeff hI hmax h𝔭 d π l)) ^ sphE hI hmax h𝔭 l := by
  have h1 : ∀ l, w (algebraMap A (Torsor hI hmax h𝔭 d hπ) (genCoeff hI hmax h𝔭 d π l)) =
      w (yU hI hmax h𝔭 hπ l) * w (torsorS hI hmax h𝔭 hπ) ^ gdeg hI hmax h𝔭 l := by
    intro l
    rw [IsScalarTower.algebraMap_apply A (ReesAlg (compFil hI hmax h𝔭 d)),
      ← torsorY_mul_s_pow hI hmax h𝔭 hd hπ l, map_mul, map_pow, map_mul, map_pow]
  rw [← mul_one (w (torsorS hI hmax h𝔭 hπ) ^ (2 * d.factorial)), ← hsph, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [h1, mul_pow, ← pow_mul, gdeg_mul_sphE hI hmax h𝔭 hd, mul_comm]

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Jou

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)

/-- The generators of the torsor over `A`. -/
def torsorGens : Set (Torsor hI hmax h𝔭 d hπ) :=
  {torsorS hI hmax h𝔭 hπ} ∪ Set.range (yU hI hmax h𝔭 hπ) ∪
    Set.range (σ (torsorY hI hmax h𝔭 d hπ))

include hd hw in
theorem torsor_adjoin : Algebra.adjoin A (torsorGens hI hmax h𝔭 hπ) = ⊤ := by
  set S := Algebra.adjoin A (torsorGens hI hmax h𝔭 hπ)
  -- the image of the Rees algebra lies in `S`
  have hR : ∀ r : ReesAlg (compFil hI hmax h𝔭 d),
      algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ) r ∈ S := by
    intro r
    have hr : (r : A[T;T⁻¹]) ∈ Algebra.adjoin A (reesGenSet hI hmax h𝔭 d) := by
      rw [← reesAlg_eq_adjoin hI hmax h𝔭 d hd hw]; exact r.2
    suffices H : ∀ p (hp : p ∈ Algebra.adjoin A (reesGenSet hI hmax h𝔭 d)),
        algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ)
          ⟨p, (reesAlg_eq_adjoin hI hmax h𝔭 d hd hw).symm ▸ hp⟩ ∈ S from H _ hr
    intro p hp
    induction hp using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact Algebra.subset_adjoin (Or.inl (Or.inl rfl))
      · simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe, Finset.mem_Icc] at hx
        obtain ⟨j, ⟨hj1, hjd⟩, g, hg, rfl⟩ := hx
        obtain ⟨l, hl1, hl2⟩ := exists_index hI hmax h𝔭 (π := π) hj1 hjd hg
        have : (⟨LaurentPolynomial.C g * T j, (reesAlg_eq_adjoin hI hmax h𝔭 d hd hw).symm ▸
            Algebra.subset_adjoin (Or.inr (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_Icc.2
              ⟨hj1, hjd⟩)) ⟨g, hg, rfl⟩))⟩ : ReesAlg (compFil hI hmax h𝔭 d)) =
            torsorY hI hmax h𝔭 d hπ l := by
          apply Subtype.ext
          simp only [torsorY, hl1, hl2]
        rw [this]
        exact Algebra.subset_adjoin (Or.inl (Or.inr ⟨l, rfl⟩))
    | algebraMap a =>
      have : (⟨algebraMap A A[T;T⁻¹] a, _⟩ : ReesAlg (compFil hI hmax h𝔭 d)) =
          algebraMap A (ReesAlg (compFil hI hmax h𝔭 d)) a := rfl
      rw [this, ← IsScalarTower.algebraMap_apply]
      exact Subalgebra.algebraMap_mem _ a
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, _⟩ : ReesAlg (compFil hI hmax h𝔭 d)) =
          ⟨x, (reesAlg_eq_adjoin hI hmax h𝔭 d hd hw).symm ▸ hx⟩ +
            ⟨y, (reesAlg_eq_adjoin hI hmax h𝔭 d hd hw).symm ▸ hy⟩ := rfl
      rw [this, map_add]; exact add_mem ihx ihy
    | mul x y hx hy ihx ihy =>
      have : (⟨x * y, _⟩ : ReesAlg (compFil hI hmax h𝔭 d)) =
          ⟨x, (reesAlg_eq_adjoin hI hmax h𝔭 d hd hw).symm ▸ hx⟩ *
            ⟨y, (reesAlg_eq_adjoin hI hmax h𝔭 d hd hw).symm ▸ hy⟩ := rfl
      rw [this, map_mul]; exact mul_mem ihx ihy
  -- the `σ` generate over the Rees algebra
  rw [eq_top_iff]
  rintro f -
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective f
  induction p using MvPolynomial.induction_on with
  | C a =>
    have := hR a
    rwa [Jou.algebraMap_eq_mk_comp_C] at this
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul]
    exact mul_mem hp (Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩))

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Jou

lemma abs_le_one_add_pow (x : ℝ) {n : ℕ} (hn : 0 < n) : |x| ≤ 1 + x ^ (2 * n) := by
  have h2 : x ^ (2 * n) = |x| ^ (2 * n) := by rw [pow_mul, pow_mul, sq_abs]
  rw [h2]
  rcases le_or_gt |x| 1 with h | h
  · have : 0 ≤ |x| ^ (2 * n) := by positivity
    linarith
  · have : |x| ≤ |x| ^ (2 * n) := le_self_pow₀ h.le (by omega)
    linarith

lemma abs_le_one_of_pow_le {x : ℝ} {n : ℕ} (hn : n ≠ 0) (he : Even n) (h : x ^ n ≤ 1) : |x| ≤ 1 := by
  rw [← he.pow_abs] at h
  exact (pow_le_one_iff_of_nonneg (abs_nonneg x) hn).1 h

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)

include hd in
lemma torsorK_y_le {K : Set (RealPt A)} {w : RealPt (Torsor hI hmax h𝔭 d hπ)}
    (hwK : w ∈ torsorK hI hmax h𝔭 hπ K) (l) : |w (yU hI hmax h𝔭 hπ l)| ≤ 1 := by
  obtain ⟨-, -, hsph, -⟩ := hwK
  refine abs_le_one_of_pow_le (sphE_pos hI hmax h𝔭 hd l).ne' (sphE_even hI hmax h𝔭 l) ?_
  rw [← hsph]
  exact Finset.single_le_sum (f := fun l' => w (yU hI hmax h𝔭 hπ l') ^ sphE hI hmax h𝔭 l')
    (fun l' _ => (sphE_even hI hmax h𝔭 l').pow_nonneg (w (yU hI hmax h𝔭 hπ l')))
    (Finset.mem_univ l)

include hd hw in
theorem torsorK_isCompact {K : Set (RealPt A)} (hK : IsCompact K) :
    IsCompact (torsorK hI hmax h𝔭 hπ K) := by
  have hclosed : IsClosed (torsorK hI hmax h𝔭 hπ K) := by
    have h1 : IsClosed {w : RealPt (Torsor hI hmax h𝔭 d hπ) |
        RealPt.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) w ∈ K} :=
      hK.isClosed.preimage (RealPt.continuous_comap _)
    have h2 : IsClosed {w : RealPt (Torsor hI hmax h𝔭 d hπ) | 0 ≤ w (torsorS hI hmax h𝔭 hπ)} :=
      isClosed_le continuous_const (RealPt.continuous_eval _)
    have h3 : IsClosed {w : RealPt (Torsor hI hmax h𝔭 d hπ) |
        ∑ l, w (yU hI hmax h𝔭 hπ l) ^ sphE hI hmax h𝔭 l = 1} :=
      isClosed_eq (continuous_finset_sum _ fun l _ => (RealPt.continuous_eval _).pow _)
        continuous_const
    have h4 : IsClosed {w : RealPt (Torsor hI hmax h𝔭 d hπ) | ∀ l,
        w (σ (torsorY hI hmax h𝔭 d hπ) l) = w (yU hI hmax h𝔭 hπ l) ^ (sphE hI hmax h𝔭 l - 1)} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun l =>
        isClosed_eq (RealPt.continuous_eval _) ((RealPt.continuous_eval _).pow _)
    exact h1.inter (h2.inter (h3.inter h4))
  refine RealPt.isCompact_of_forall_bounded hclosed fun x => ?_
  refine RealPt.forall_bounded_of_gen hK (fun w hw => hw.1) (torsor_adjoin hI hmax h𝔭 hd hw hπ)
    ?_ x
  rintro _ ((h | ⟨l, rfl⟩) | ⟨l, rfl⟩)
  · rw [Set.mem_singleton_iff] at h
    subst h
    -- bounds for the coefficients on `K`
    have hC : ∀ l, ∃ C : ℝ, ∀ z ∈ K, |z (genCoeff hI hmax h𝔭 d π l)| ≤ C := fun l => by
      obtain ⟨C, hC⟩ := (hK.image (RealPt.continuous_eval (genCoeff hI hmax h𝔭 d π l))).isBounded.exists_norm_le
      exact ⟨C, fun z hz => by simpa [Real.norm_eq_abs] using hC _ ⟨z, hz, rfl⟩⟩
    choose C hC using hC
    refine ⟨1 + ∑ l, C l ^ sphE hI hmax h𝔭 l, fun w hwK => ?_⟩
    have hs := s_pow_eq hI hmax h𝔭 hd hπ w hwK.2.2.1
    refine (abs_le_one_add_pow _ (Nat.factorial_pos d)).trans ?_
    rw [hs]
    have hsum : ∑ l, w (algebraMap A (Torsor hI hmax h𝔭 d hπ) (genCoeff hI hmax h𝔭 d π l)) ^
        sphE hI hmax h𝔭 l ≤ ∑ l, C l ^ sphE hI hmax h𝔭 l := Finset.sum_le_sum fun l _ => ?_
    · linarith
    have hz := hC l _ hwK.1
    rw [RealPt.comap_apply] at hz
    rw [← (sphE_even hI hmax h𝔭 l).pow_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hz _
  · exact ⟨1, fun w hwK => torsorK_y_le hI hmax h𝔭 hd hπ hwK l⟩
  · refine ⟨1, fun w hwK => ?_⟩
    rw [hwK.2.2.2 l, abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (torsorK_y_le hI hmax h𝔭 hd hπ hwK l)

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Jou

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)

/-- The weighted norm `∑ gₗ^{Eₗ}` at a real point of `A`. -/
def gNorm (d : ℕ) (π : A) (z : RealPt A) : ℝ :=
  ∑ l, z (genCoeff hI hmax h𝔭 d π l) ^ sphE hI hmax h𝔭 (d := d) l

lemma gNorm_nonneg (z : RealPt A) : 0 ≤ gNorm hI hmax h𝔭 d π z :=
  Finset.sum_nonneg fun l _ => (sphE_even hI hmax h𝔭 l).pow_nonneg _

/-- The `2d!`-th root of the weighted norm. -/
def gRoot (d : ℕ) (π : A) (z : RealPt A) : ℝ :=
  gNorm hI hmax h𝔭 d π z ^ (((2 * d.factorial : ℕ) : ℝ)⁻¹)

lemma gRoot_pos {z : RealPt A} (hz : 0 < gNorm hI hmax h𝔭 d π z) : 0 < gRoot hI hmax h𝔭 d π z :=
  Real.rpow_pos_of_pos hz _

lemma gRoot_pow (z : RealPt A) :
    gRoot hI hmax h𝔭 d π z ^ (2 * d.factorial) = gNorm hI hmax h𝔭 d π z :=
  Real.rpow_inv_natCast_pow (gNorm_nonneg hI hmax h𝔭 z) (by positivity)

/-- The Rees real point over `z` with `s ↦ gRoot z`. -/
def ptA_R (z : RealPt A) (hz : 0 < gNorm hI hmax h𝔭 d π z) :
    RealPt (ReesAlg (compFil hI hmax h𝔭 d)) :=
  reesPt _ (RealPt.toHom z) (Units.mk0 (gRoot hI hmax h𝔭 d π z) (gRoot_pos hI hmax h𝔭 hz).ne')⁻¹

include hd in
lemma ptA_R_y (z : RealPt A) (hz : 0 < gNorm hI hmax h𝔭 d π z) (l) :
    ptA_R hI hmax h𝔭 z hz (torsorY hI hmax h𝔭 d hπ l) =
      z (genCoeff hI hmax h𝔭 d π l) * (gRoot hI hmax h𝔭 d π z ^ gdeg hI hmax h𝔭 l)⁻¹ := by
  rw [ptA_R, torsorY, reesPt_C_mul_T _ _ _ (genCoeff_mem hI hmax h𝔭 d hπ l),
    ← gdeg_cast hI hmax h𝔭 hd l, zpow_natCast,
    Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow]
  rfl

include hd in
lemma ptA_R_sph (z : RealPt A) (hz : 0 < gNorm hI hmax h𝔭 d π z) :
    ∑ l, ptA_R hI hmax h𝔭 z hz (torsorY hI hmax h𝔭 d hπ l) ^ sphE hI hmax h𝔭 l = 1 := by
  have hcpow := gRoot_pow hI hmax h𝔭 (d := d) (π := π) z
  simp_rw [ptA_R_y hI hmax h𝔭 hd hπ z hz, mul_pow, inv_pow, ← pow_mul,
    gdeg_mul_sphE hI hmax h𝔭 hd, ← Finset.sum_mul, hcpow]
  exact mul_inv_cancel₀ hz.ne'

include hd in
lemma ptA_rel (z : RealPt A) (hz : 0 < gNorm hI hmax h𝔭 d π z) :
    ∑ l, ptA_R hI hmax h𝔭 z hz (torsorY hI hmax h𝔭 d hπ l) ^ (sphE hI hmax h𝔭 l - 1) *
      ptA_R hI hmax h𝔭 z hz (torsorY hI hmax h𝔭 d hπ l) = 1 := by
  rw [← ptA_R_sph hI hmax h𝔭 hd hπ z hz]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← pow_succ, Nat.sub_add_cancel (sphE_pos hI hmax h𝔭 hd l)]

/-- **The point of the torsor over `z ∉ V(𝔭)`.** -/
def ptA (z : RealPt A) (hz : 0 < gNorm hI hmax h𝔭 d π z) : RealPt (Torsor hI hmax h𝔭 d hπ) :=
  jPt (torsorY hI hmax h𝔭 d hπ) (RealPt.toHom (ptA_R hI hmax h𝔭 z hz))
    (fun l => ptA_R hI hmax h𝔭 z hz (torsorY hI hmax h𝔭 d hπ l) ^ (sphE hI hmax h𝔭 l - 1))
    (ptA_rel hI hmax h𝔭 hd hπ z hz)

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Jou

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)

lemma ptA_algebraMap (z : RealPt A) (hz : 0 < gNorm hI hmax h𝔭 d π z)
    (r : ReesAlg (compFil hI hmax h𝔭 d)) :
    ptA hI hmax h𝔭 hd hπ z hz (algebraMap _ (Torsor hI hmax h𝔭 d hπ) r) = ptA_R hI hmax h𝔭 z hz r :=
  jPt_algebraMap _ _ _ _ r

lemma ptA_σ (z : RealPt A) (hz : 0 < gNorm hI hmax h𝔭 d π z) (l) :
    ptA hI hmax h𝔭 hd hπ z hz (σ (torsorY hI hmax h𝔭 d hπ) l) =
      ptA_R hI hmax h𝔭 z hz (torsorY hI hmax h𝔭 d hπ l) ^ (sphE hI hmax h𝔭 l - 1) :=
  jPt_σ _ _ _ _ l

lemma ptA_comap (z : RealPt A) (hz : 0 < gNorm hI hmax h𝔭 d π z) :
    RealPt.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) (ptA hI hmax h𝔭 hd hπ z hz) = z := by
  ext a
  rw [RealPt.comap_apply, IsScalarTower.algebraMap_apply A (ReesAlg (compFil hI hmax h𝔭 d)),
    ptA_algebraMap, ptA_R, reesPt_algebraMap]
  rfl

lemma ptA_s (z : RealPt A) (hz : 0 < gNorm hI hmax h𝔭 d π z) :
    ptA hI hmax h𝔭 hd hπ z hz (torsorS hI hmax h𝔭 hπ) = gRoot hI hmax h𝔭 d π z := by
  rw [torsorS, ptA_algebraMap, ptA_R, reesPt_s]
  simp

lemma ptA_mem (K : Set (RealPt A)) {z : RealPt A} (hzK : z ∈ K)
    (hz : 0 < gNorm hI hmax h𝔭 d π z) : ptA hI hmax h𝔭 hd hπ z hz ∈ torsorK hI hmax h𝔭 hπ K := by
  refine ⟨by rw [ptA_comap]; exact hzK, ?_, ?_, fun l => ?_⟩
  · rw [ptA_s]; exact (gRoot_pos hI hmax h𝔭 hz).le
  · simp only [yU, ptA_algebraMap]
    exact ptA_R_sph hI hmax h𝔭 hd hπ z hz
  · simp only [yU, ptA_algebraMap, ptA_σ]

/-- **Uniqueness over `z ∉ V(𝔭)`.** -/
theorem eq_ptA (K : Set (RealPt A)) {w : RealPt (Torsor hI hmax h𝔭 d hπ)}
    (hwK : w ∈ torsorK hI hmax h𝔭 hπ K) {z : RealPt A}
    (hwz : RealPt.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) w = z)
    (hz : 0 < gNorm hI hmax h𝔭 d π z) : w = ptA hI hmax h𝔭 hd hπ z hz := by
  obtain ⟨-, hs0, hsph, hσ⟩ := hwK
  have hpow := s_pow_eq hI hmax h𝔭 hd hπ w hsph
  have hgz : ∑ l, w (algebraMap A _ (genCoeff hI hmax h𝔭 d π l)) ^ sphE hI hmax h𝔭 l =
      gNorm hI hmax h𝔭 d π z := by
    rw [gNorm, ← hwz]; rfl
  rw [hgz, ← gRoot_pow hI hmax h𝔭 z] at hpow
  have hsw : w (torsorS hI hmax h𝔭 hπ) = gRoot hI hmax h𝔭 d π z :=
    (pow_left_inj₀ hs0 (gRoot_pos hI hmax h𝔭 hz).le (by positivity)).1 hpow
  -- the restriction to the Rees algebra
  set wR := RealPt.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ)) w
  have hwRs : wR (reesS _ (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj)) =
      gRoot hI hmax h𝔭 d π z := hsw
  have hwR := reesPt_eq _ (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj) wR
    (by rw [hwRs]; exact (gRoot_pos hI hmax h𝔭 hz).ne')
  have hcomp : (RealPt.toHom wR).comp (algebraMap A (ReesAlg (compFil hI hmax h𝔭 d))) =
      RealPt.toHom z := by
    ext a
    rw [← hwz]
    simp only [RingHom.comp_apply, RealPt.toHom_apply, RealPt.comap_apply, wR]
    rw [← IsScalarTower.algebraMap_apply]
  have hwR' : wR = ptA_R hI hmax h𝔭 z hz := by
    rw [hwR, ptA_R, hcomp]
    congr 2
    exact Units.ext hwRs
  apply realPt_J_ext
  · intro r
    show wR r = _
    rw [hwR', ptA_algebraMap]
  · intro l
    rw [hσ l, ptA_σ]
    show wR _ ^ _ = _
    rw [hwR']

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Jou IsLocalRing

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)

/-- **Local presentation data** at a real point `z` of `V(𝔭)`. -/
structure LocPres (z : RealPt A) where
  𝔪 : Ideal A
  [h𝔪 : 𝔪.IsMaximal]
  n : ℕ
  k : ℕ
  hkn : k ≤ n
  c : Chart (Localization.AtPrime 𝔪) n
  hc : c.IsCentred
  e : Fin n → ℚ
  he : ∀ i, 0 ≤ e i
  hle1 : ∀ i, e i ≤ 1
  hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) < k
  hev : ∀ i : Fin n, e i = v₀ i
  hk2 : v₀ 1 ≠ 0 → 2 ≤ k
  w : Fin n → ℕ
  hw : ∀ i, (w i : ℚ) = d * e i
  hF : ∀ j, ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime 𝔪)).F j = chartFil c e d j
  z𝔪 : Localization.AtPrime 𝔪 →+* ℝ
  hz𝔪 : ∀ a, z𝔪 (algebraMap A _ a) = z a
  hP : 𝔭.map (algebraMap A (Localization.AtPrime 𝔪)) = Ideal.span (c.x '' {i | (i : ℕ) < k})

attribute [instance] LocPres.h𝔪

include hw in
/-- Local presentation data exist at every real point killing `𝔭`. -/
theorem LocPres.nonempty (z : RealPt A) (hz : ∀ g ∈ 𝔭, z g = 0) :
    Nonempty (LocPres hI hmax h𝔭 (d := d) z) := by
  classical
  set 𝔮 := RingHom.ker (RealPt.toHom z)
  have h𝔮 : 𝔮 ≠ ⊤ := by
    intro h
    have : (1 : A) ∈ 𝔮 := h ▸ Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at this
    exact one_ne_zero this
  obtain ⟨𝔪, h𝔪, h𝔮𝔪⟩ := Ideal.exists_le_maximal 𝔮 h𝔮
  haveI := h𝔪
  have h𝔭𝔪 : 𝔭 ≤ 𝔪 := fun g hg => h𝔮𝔪 (by rw [RingHom.mem_ker]; exact hz g hg)
  obtain ⟨hI𝔪, hv⟩ := mem_maxLocus_of_minimal hI hmax h𝔭 𝔪 h𝔭𝔪
  obtain ⟨D⟩ := LocData.nonempty hI 𝔪 hI𝔪 hv
  -- the extension of `z` to the local ring
  have hunit : ∀ m : 𝔪.primeCompl, IsUnit ((RealPt.toHom z) (m : A)) := fun m => by
    rw [isUnit_iff_ne_zero]
    intro h0
    exact m.2 (h𝔮𝔪 (by rw [RingHom.mem_ker]; exact h0))
  set z𝔪 : Localization.AtPrime 𝔪 →+* ℝ := IsLocalization.lift hunit
  have hz𝔪 : ∀ a, z𝔪 (algebraMap A _ a) = z a := fun a => IsLocalization.lift_eq hunit a
  have hev : ∀ i : Fin D.n, D.ek i = v₀ i := fun i => by
    have := congrFun D.hv (i : ℕ); rw [ext0_apply] at this; exact this
  choose w hw' using fun i : Fin D.n => hw i
  set k' := min D.k D.n
  have hsupp' : ∀ i : Fin D.n, D.ek i ≠ 0 ↔ (i : ℕ) < k' := fun i => by
    rw [D.supp i]; have := i.2; omega
  refine ⟨⟨𝔪, D.n, k', min_le_right _ _, Loc.transport (D.ctrl 𝔪 D.hg) D.ck, D.cent, D.ek,
    D.inv.nonneg, fun i => D.inv.le_one (Iloc_le hI𝔪) i, hsupp', hev, fun h1 => ?_, w, fun i => by rw [hw' i, hev i], fun j => ?_, z𝔪, hz𝔪, ?_⟩⟩
  · have hv1 := congrFun D.hv 1
    by_cases hn : 1 < D.n
    · simp only [ext0, dif_pos hn] at hv1
      have hne : D.ek ⟨1, hn⟩ ≠ 0 := by rw [hv1]; exact h1
      have h2 : (1 : ℕ) < D.k := (D.supp ⟨1, hn⟩).1 hne
      simp only [k']; omega
    · simp only [ext0, dif_neg hn] at hv1
      exact absurd hv1.symm h1
  · rw [compFil_loc_F hI hmax h𝔭 d 𝔪 h𝔭𝔪, D.cRF_eq_transport hI]; rfl
  · have h1 := D.map_p
    rw [← D.eq_p_of_minimal h𝔭 h𝔭𝔪] at h1
    rw [h1, LocData.P]
    congr 2
    ext i
    simp only [Set.mem_setOf_eq]
    have := i.2; omega

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Jou IsLocalRing MvPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  {z : RealPt A} (hz : ∀ g ∈ 𝔭, z g = 0) (P : LocPres hI hmax h𝔭 (d := d) z)

/-- The presentation of the local Rees algebra. -/
abbrev LocPres.psi : MvPolynomial (Option (Fin P.k)) (Localization.AtPrime P.𝔪) →ₐ[Localization.AtPrime P.𝔪]
    ReesAlg ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime P.𝔪)) :=
  reesPsi P.c P.hF P.he hd P.hw P.hkn

lemma LocPres.psi_surj : Function.Surjective (P.psi hI hmax h𝔭 hd) :=
  reesPsi_surjective P.c P.hF P.he hd P.hw P.hkn P.hsupp

/-- Evaluation at `s = 0`, `u`. -/
def LocPres.ev (u : Fin P.k → ℝ) : MvPolynomial (Option (Fin P.k)) (Localization.AtPrime P.𝔪) →+* ℝ :=
  eval₂Hom P.z𝔪 (fun o => o.elim 0 u)

include hz in
lemma LocPres.z𝔪_x (i : Fin P.k) : P.z𝔪 (P.c.x (ιk P.hkn i)) = 0 := by
  have hmem : P.c.x (ιk P.hkn i) ∈ 𝔭.map (algebraMap A (Localization.AtPrime P.𝔪)) := by
    rw [P.hP]
    exact Ideal.subset_span ⟨ιk P.hkn i, by simp [ιk], rfl⟩
  have hle : 𝔭.map (algebraMap A (Localization.AtPrime P.𝔪)) ≤ RingHom.ker P.z𝔪 := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker, P.hz𝔪]
    exact hz g hg
  exact hle hmem

include hd hz in
lemma LocPres.ev_kills (u : Fin P.k → ℝ) :
    RingHom.ker (P.psi hI hmax h𝔭 hd).toRingHom ≤ RingHom.ker (P.ev hI hmax h𝔭 u) := by
  have hker := reesPsi_ker P.c P.hc P.hF P.he hd P.hw P.hkn P.hsupp
  rw [show RingHom.ker (P.psi hI hmax h𝔭 hd).toRingHom =
    RingHom.ker (reesPsi P.c P.hF P.he hd P.hw P.hkn) from rfl, hker, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker, reesRel, LocPres.ev, map_sub, map_mul, map_pow,
    eval₂Hom_C, eval₂Hom_X', eval₂Hom_X', P.z𝔪_x hI hmax h𝔭 hz i]
  have hw0 : P.w (ιk P.hkn i) ≠ 0 := by
    intro h0
    have hne : P.e (ιk P.hkn i) ≠ 0 := (P.hsupp _).2 (by simp [ιk])
    have := P.hw (ιk P.hkn i)
    rw [h0, Nat.cast_zero] at this
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    exact hne ((mul_eq_zero.1 this.symm).resolve_left hdq)
  simp [zero_pow hw0]

/-- The real point `ψ_u` of the local Rees algebra. -/
def LocPres.psiPt (u : Fin P.k → ℝ) :
    ReesAlg ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime P.𝔪)) →+* ℝ :=
  (Ideal.Quotient.lift _ (P.ev hI hmax h𝔭 u)
    (fun a ha => (RingHom.mem_ker).1 (P.ev_kills hI hmax h𝔭 hd hz u ha))).comp
    (RingHom.quotientKerEquivOfSurjective (P.psi_surj hI hmax h𝔭 hd)).symm.toRingHom

lemma LocPres.psiPt_psi (u : Fin P.k → ℝ) (p) :
    P.psiPt hI hmax h𝔭 hd hz u (P.psi hI hmax h𝔭 hd p) = P.ev hI hmax h𝔭 u p := by
  rw [LocPres.psiPt, RingHom.comp_apply]
  have : (RingHom.quotientKerEquivOfSurjective (P.psi_surj hI hmax h𝔭 hd)).symm
      (P.psi hI hmax h𝔭 hd p) = Ideal.Quotient.mk _ p := by
    rw [RingEquiv.symm_apply_eq]; rfl
  rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this, Ideal.Quotient.lift_mk]

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Jou IsLocalRing MvPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  {z : RealPt A} (hz : ∀ g ∈ 𝔭, z g = 0) (P : LocPres hI hmax h𝔭 (d := d) z)

/-- The real point `Ψ(u)` of the global Rees algebra. -/
def LocPres.Psi (u : Fin P.k → ℝ) : RealPt (ReesAlg (compFil hI hmax h𝔭 d)) :=
  RealPt.ofHom ((P.psiPt hI hmax h𝔭 hd hz u).comp
    (reesMap (compFil hI hmax h𝔭 d) (Localization.AtPrime P.𝔪)))

lemma LocPres.Psi_apply (u : Fin P.k → ℝ) (p : ReesAlg (compFil hI hmax h𝔭 d)) :
    P.Psi hI hmax h𝔭 hd hz u p =
      P.psiPt hI hmax h𝔭 hd hz u (reesMap _ (Localization.AtPrime P.𝔪) p) := rfl

lemma LocPres.reesMap_algebraMap (a : A) :
    reesMap (compFil hI hmax h𝔭 d) (Localization.AtPrime P.𝔪)
        (algebraMap A (ReesAlg (compFil hI hmax h𝔭 d)) a) =
      P.psi hI hmax h𝔭 hd (C (algebraMap A (Localization.AtPrime P.𝔪) a)) := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  apply Subtype.ext
  rw [reesMap_coe]
  show lmap _ (algebraMap A A[T;T⁻¹] a) = algebraMap (Localization.AtPrime P.𝔪) _ _
  rw [← LaurentPolynomial.C_eq_algebraMap, ← LaurentPolynomial.C_eq_algebraMap]
  have := lmap_C_mul_T (algebraMap A (Localization.AtPrime P.𝔪)) a 0
  simp only [T_zero, mul_one] at this
  exact this

lemma LocPres.Psi_algebraMap (u : Fin P.k → ℝ) (a : A) :
    P.Psi hI hmax h𝔭 hd hz u (algebraMap A (ReesAlg (compFil hI hmax h𝔭 d)) a) = z a := by
  rw [LocPres.Psi_apply, LocPres.reesMap_algebraMap hI hmax h𝔭 hd P a, LocPres.psiPt_psi,
    LocPres.ev, eval₂Hom_C, P.hz𝔪]

lemma LocPres.reesMap_s :
    reesMap (compFil hI hmax h𝔭 d) (Localization.AtPrime P.𝔪)
        (reesS _ (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj)) =
      P.psi hI hmax h𝔭 hd (X none) := by
  rw [LocPres.psi, reesPsi, aeval_X]
  apply Subtype.ext
  rw [reesMap_coe, reesS_coe]
  simp only [reesGen, Option.elim, reesX_last]
  have := lmap_C_mul_T (algebraMap A (Localization.AtPrime P.𝔪)) 1 (-1)
  simp only [map_one, one_mul] at this
  exact this

lemma LocPres.Psi_s (u : Fin P.k → ℝ) :
    P.Psi hI hmax h𝔭 hd hz u (reesS _ (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj)) = 0 := by
  rw [LocPres.Psi_apply, LocPres.reesMap_s hI hmax h𝔭 hd P, LocPres.psiPt_psi, LocPres.ev,
    eval₂Hom_X']
  rfl

lemma LocPres.psiPt_u (u : Fin P.k → ℝ) (i : Fin P.k) :
    P.psiPt hI hmax h𝔭 hd hz u (reesX P.c P.hF P.he hd P.hw (Fin.castSucc (ιk P.hkn i))) = u i := by
  have : reesX P.c P.hF P.he hd P.hw (Fin.castSucc (ιk P.hkn i)) = P.psi hI hmax h𝔭 hd (X (some i)) := by
    rw [LocPres.psi, reesPsi, aeval_X]; rfl
  rw [this, LocPres.psiPt_psi, LocPres.ev, eval₂Hom_X']
  rfl

lemma LocPres.continuous_Psi : Continuous fun u => P.Psi hI hmax h𝔭 hd hz u := by
  rw [RealPt.continuous_iff]
  intro p
  obtain ⟨Q, hQ⟩ := P.psi_surj hI hmax h𝔭 hd (reesMap _ (Localization.AtPrime P.𝔪) p)
  simp only [LocPres.Psi_apply, ← hQ, LocPres.psiPt_psi, LocPres.ev, coe_eval₂Hom]
  clear hQ
  induction Q using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.eval₂_C]; exact continuous_const
  | add p q hp hq => simp only [MvPolynomial.eval₂_add]; exact hp.add hq
  | mul_X p o hp =>
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    refine hp.mul ?_
    cases o with
    | none => exact continuous_const
    | some i => exact continuous_apply i

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Jou IsLocalRing MvPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  {z : RealPt A} (hz : ∀ g ∈ 𝔭, z g = 0) (P : LocPres hI hmax h𝔭 (d := d) z)

/-- **Every real point over `z` on the exceptional divisor is some `Ψ(u)`.** -/
theorem LocPres.eq_Psi (wR : RealPt (ReesAlg (compFil hI hmax h𝔭 d)))
    (hA : ∀ a, wR (algebraMap A _ a) = z a)
    (hs : wR (reesS _ (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj)) = 0) :
    ∃ u, wR = P.Psi hI hmax h𝔭 hd hz u := by
  letI := (reesMap (compFil hI hmax h𝔭 d) (Localization.AtPrime P.𝔪)).toAlgebra
  haveI hloc := reesMap_isLocalization (compFil hI hmax h𝔭 d) (Localization.AtPrime P.𝔪)
    P.𝔪.primeCompl (Ideal.primeCompl_le_nonZeroDivisors P.𝔪)
  have hunit : ∀ m : P.𝔪.primeCompl.map (algebraMap A (ReesAlg (compFil hI hmax h𝔭 d))),
      IsUnit ((RealPt.toHom wR) (m : ReesAlg (compFil hI hmax h𝔭 d))) := by
    rintro ⟨_, m, hm, rfl⟩
    rw [RealPt.toHom_apply, hA, isUnit_iff_ne_zero, ← P.hz𝔪]
    exact (IsLocalization.map_units (Localization.AtPrime P.𝔪) (⟨m, hm⟩ : P.𝔪.primeCompl)).map
      P.z𝔪 |>.ne_zero
  set w' : ReesAlg ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime P.𝔪)) →+* ℝ :=
    IsLocalization.lift hunit
  have hw' : ∀ p, w' (reesMap _ (Localization.AtPrime P.𝔪) p) = wR p := fun p =>
    IsLocalization.lift_eq hunit p
  refine ⟨fun i => w' (reesX P.c P.hF P.he hd P.hw (Fin.castSucc (ιk P.hkn i))), ?_⟩
  -- `w'` agrees with `z𝔪` on the local ring
  have hbase : w'.comp (algebraMap (Localization.AtPrime P.𝔪) _) = P.z𝔪 := by
    refine IsLocalization.ringHom_ext P.𝔪.primeCompl (RingHom.ext fun a => ?_)
    simp only [RingHom.comp_apply]
    rw [P.hz𝔪, ← hA, ← hw']
    congr 1
    rw [LocPres.reesMap_algebraMap hI hmax h𝔭 hd P a, ← MvPolynomial.algebraMap_eq,
      AlgHom.commutes]
  have hcomp : w'.comp (P.psi hI hmax h𝔭 hd).toRingHom =
      P.ev hI hmax h𝔭 (fun i => w' (reesX P.c P.hF P.he hd P.hw (Fin.castSucc (ιk P.hkn i)))) := by
    refine MvPolynomial.ringHom_ext (fun b => ?_) (fun o => ?_)
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, LocPres.ev,
        eval₂Hom_C]
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, ← RingHom.comp_apply, hbase]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, LocPres.ev,
        eval₂Hom_X']
      cases o with
      | none =>
        rw [← LocPres.reesMap_s hI hmax h𝔭 hd P, hw', hs]; rfl
      | some i =>
        show w' (P.psi hI hmax h𝔭 hd (X (some i))) = _
        rw [LocPres.psi, reesPsi, aeval_X]; rfl
  have heq : w' = P.psiPt hI hmax h𝔭 hd hz
      (fun i => w' (reesX P.c P.hF P.he hd P.hw (Fin.castSucc (ιk P.hkn i)))) := by
    ext q
    obtain ⟨p, rfl⟩ := P.psi_surj hI hmax h𝔭 hd q
    rw [LocPres.psiPt_psi, ← hcomp]
    rfl
  ext p
  rw [LocPres.Psi_apply, ← heq, hw']

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Jou IsLocalRing MvPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  {z : RealPt A} (hz : ∀ g ∈ 𝔭, z g = 0) (P : LocPres hI hmax h𝔭 (d := d) z)

/-- The weighted scaling `c ⋆ u`. -/
def LocPres.scale (c : ℝ) (u : Fin P.k → ℝ) : Fin P.k → ℝ :=
  fun i => c ^ P.w (ιk P.hkn i) * u i

/-- The values on the Rees coordinates `xᵢ T^{wᵢ}` scale with weight `wᵢ` (where they matter). -/
lemma LocPres.psiPt_reesX_scale (c : ℝ) (u : Fin P.k → ℝ) (i : Fin P.n) (hi : (i : ℕ) < P.k) :
    P.psiPt hI hmax h𝔭 hd hz (P.scale hI hmax h𝔭 c u) (reesX P.c P.hF P.he hd P.hw (Fin.castSucc i)) =
      c ^ P.w i * P.psiPt hI hmax h𝔭 hd hz u (reesX P.c P.hF P.he hd P.hw (Fin.castSucc i)) := by
  have hι : ιk P.hkn ⟨i, hi⟩ = i := Fin.ext rfl
  have h1 := P.psiPt_u hI hmax h𝔭 hd hz (P.scale hI hmax h𝔭 c u) ⟨i, hi⟩
  have h2 := P.psiPt_u hI hmax h𝔭 hd hz u ⟨i, hi⟩
  rw [hι] at h1 h2
  rw [h1, h2, LocPres.scale, hι]

set_option maxHeartbeats 1000000 in
/-- **Weighted homogeneity** of the fibre coordinates. -/
theorem LocPres.psiPt_scale (c : ℝ) (u : Fin P.k → ℝ) (j : ℕ) {g : Localization.AtPrime P.𝔪}
    (hg : g ∈ chartFil P.c P.e d j)
    (h : LaurentPolynomial.C g * T j ∈ ReesAlg ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime P.𝔪))) :
    P.psiPt hI hmax h𝔭 hd hz (P.scale hI hmax h𝔭 c u) ⟨_, h⟩ =
      c ^ j * P.psiPt hI hmax h𝔭 hd hz u ⟨_, h⟩ := by
  classical
  set R' := ReesAlg ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime P.𝔪))
  have hFj : ∀ {g'}, g' ∈ chartFil P.c P.e d j → LaurentPolynomial.C g' * T j ∈ R' := fun hg' =>
    C_mul_T_mem_ReesAlg (by rw [P.hF]; exact hg')
  revert h
  rw [chartFil, Chart.RF] at hg
  induction hg using Submodule.span_induction with
  | mem g hmem =>
    intro h
    obtain ⟨α, hα0, hα1, rfl⟩ := hmem
    -- the weight of `α`
    set wα : ℕ := ∑ i, α i * P.w i
    have hdq : (0 : ℚ) < d := by exact_mod_cast hd
    have hjw : j ≤ wα := by
      have : ((j : ℤ) : ℚ) / d ≤ lam P.e α := hα1
      have hl : lam P.e α = (wα : ℚ) / d := by
        rw [lam]; simp only [wα]; push_cast
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [P.hw i]; field_simp
      rw [hl] at this
      push_cast at this
      exact_mod_cast (div_le_div_iff_of_pos_right hdq).1 this
    have hid : (⟨LaurentPolynomial.C (∏ i, P.c.x i ^ α i) * T j, h⟩ : R') =
        (∏ i, reesX P.c P.hF P.he hd P.hw (Fin.castSucc i) ^ α i) *
          reesX P.c P.hF P.he hd P.hw (Fin.last P.n) ^ (wα - j) := by
      apply Subtype.ext
      rw [Subalgebra.coe_mul, SubmonoidClass.coe_finset_prod, SubmonoidClass.coe_pow, reesX_last]
      simp only [SubmonoidClass.coe_pow, reesX_castSucc, mul_pow, T_pow, Finset.prod_mul_distrib,
        ← map_pow, ← map_prod, prod_T_eq, mul_assoc, ← T_add]
      congr 2
      rw [Nat.cast_sub hjw]
      simp only [wα]
      push_cast
      ring
    rw [hid]
    simp only [map_mul, map_prod, map_pow]
    have hs0 : ∀ u', P.psiPt hI hmax h𝔭 hd hz u' (reesX P.c P.hF P.he hd P.hw (Fin.last P.n)) = 0 := by
      intro u'
      have := LocPres.reesMap_s hI hmax h𝔭 hd P
      have h2 : reesX P.c P.hF P.he hd P.hw (Fin.last P.n) = P.psi hI hmax h𝔭 hd (X none) := by
        rw [LocPres.psi, reesPsi, aeval_X]; rfl
      rw [h2, LocPres.psiPt_psi, LocPres.ev, eval₂Hom_X']; rfl
    rw [hs0, hs0]
    rcases Nat.eq_zero_or_pos (wα - j) with hm | hm
    · have hwj : wα = j := by omega
      simp only [hm, pow_zero, mul_one]
      have hprod : ∀ i ∈ Finset.univ, P.psiPt hI hmax h𝔭 hd hz (P.scale hI hmax h𝔭 c u)
          (reesX P.c P.hF P.he hd P.hw (Fin.castSucc i)) ^ α i =
          (c ^ P.w i) ^ α i * P.psiPt hI hmax h𝔭 hd hz u
            (reesX P.c P.hF P.he hd P.hw (Fin.castSucc i)) ^ α i := by
        intro i _
        by_cases hαi : α i = 0
        · rw [hαi, pow_zero, pow_zero, pow_zero, one_mul]
        · have hei : P.e i ≠ 0 := fun h0 => hαi (hα0 i h0)
          rw [P.psiPt_reesX_scale hI hmax h𝔭 hd hz c u i ((P.hsupp i).1 hei), mul_pow]
      rw [Finset.prod_congr rfl hprod, Finset.prod_mul_distrib, ← hwj]
      congr 1
      simp only [wα, ← pow_mul, Finset.prod_pow_eq_pow_sum, mul_comm]
    · rw [zero_pow hm.ne', mul_zero, mul_zero, mul_zero]
  | zero =>
    intro h
    have : (⟨LaurentPolynomial.C 0 * T j, h⟩ : R') = 0 := Subtype.ext (by simp)
    rw [this, map_zero, map_zero, mul_zero]
  | add x y hx hy ihx ihy =>
    intro h
    have hx' : LaurentPolynomial.C x * T j ∈ R' := hFj (g' := x) (by rw [chartFil, Chart.RF]; exact hx)
    have hy' : LaurentPolynomial.C y * T j ∈ R' := hFj (g' := y) (by rw [chartFil, Chart.RF]; exact hy)
    have : (⟨LaurentPolynomial.C (x + y) * T j, h⟩ : R') = ⟨_, hx'⟩ + ⟨_, hy'⟩ := by
      apply Subtype.ext
      show LaurentPolynomial.C (x + y) * T j = LaurentPolynomial.C x * T j + LaurentPolynomial.C y * T j
      rw [map_add, add_mul]
    rw [this, map_add, map_add, ihx hx', ihy hy', mul_add]
    all_goals first | exact hx' | exact hy' 
  | smul b x hx ih =>
    intro h
    have hx' : LaurentPolynomial.C x * T j ∈ R' := hFj (g' := x) (by rw [chartFil, Chart.RF]; exact hx)
    have : (⟨LaurentPolynomial.C (b • x) * T j, h⟩ : R') =
        algebraMap (Localization.AtPrime P.𝔪) R' b * ⟨_, hx'⟩ := by
      apply Subtype.ext
      show LaurentPolynomial.C (b • x) * T j =
        algebraMap (Localization.AtPrime P.𝔪) _ b * (LaurentPolynomial.C x * T j)
      rw [smul_eq_mul, map_mul, ← LaurentPolynomial.C_eq_algebraMap, mul_assoc]
    rw [this, map_mul, map_mul, ih hx']
    have hb : ∀ u', P.psiPt hI hmax h𝔭 hd hz u' (algebraMap (Localization.AtPrime P.𝔪) R' b) =
        P.z𝔪 b := by
      intro u'
      rw [← AlgHom.commutes (P.psi hI hmax h𝔭 hd) b, MvPolynomial.algebraMap_eq,
        LocPres.psiPt_psi, LocPres.ev, eval₂Hom_C]
    rw [hb, hb]
    · ring
    all_goals exact hx' 

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Jou IsLocalRing MvPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  {z : RealPt A} (hz : ∀ g ∈ 𝔭, z g = 0) (P : LocPres hI hmax h𝔭 (d := d) z)
  {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)

/-- **Weighted homogeneity** of the torsor generators on the fibre. -/
theorem LocPres.Psi_scale_y (c : ℝ) (u : Fin P.k → ℝ) (l : Fin (nGen hI hmax h𝔭 d + 1)) :
    P.Psi hI hmax h𝔭 hd hz (P.scale hI hmax h𝔭 c u) (torsorY hI hmax h𝔭 d hπ l) =
      c ^ gdeg hI hmax h𝔭 l * P.Psi hI hmax h𝔭 hd hz u (torsorY hI hmax h𝔭 d hπ l) := by
  set g' := algebraMap A (Localization.AtPrime P.𝔪) (genCoeff hI hmax h𝔭 d π l)
  have hg : g' ∈ chartFil P.c P.e d (gdeg hI hmax h𝔭 l) := by
    rw [← P.hF, gdeg_cast hI hmax h𝔭 hd]
    exact Ideal.mem_map_of_mem _ (genCoeff_mem hI hmax h𝔭 d hπ l)
  have hmem : LaurentPolynomial.C g' * T (gdeg hI hmax h𝔭 l) ∈
      ReesAlg ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime P.𝔪)) :=
    C_mul_T_mem_ReesAlg (by rw [P.hF]; exact hg)
  have hmap : reesMap _ (Localization.AtPrime P.𝔪) (torsorY hI hmax h𝔭 d hπ l) = ⟨_, hmem⟩ := by
    apply Subtype.ext
    rw [reesMap_coe]
    show lmap _ (LaurentPolynomial.C (genCoeff hI hmax h𝔭 d π l) * T (genDeg hI hmax h𝔭 d l)) =
      LaurentPolynomial.C g' * T (gdeg hI hmax h𝔭 l)
    rw [lmap_C_mul_T, gdeg_cast hI hmax h𝔭 hd]
  rw [LocPres.Psi_apply, LocPres.Psi_apply, hmap]
  exact P.psiPt_scale hI hmax h𝔭 hd hz c u _ hg hmem

/-- If all torsor generators vanish at `Ψ(u)`, then `u = 0`. -/
theorem LocPres.eq_zero_of_Psi_y (u : Fin P.k → ℝ)
    (h0 : ∀ l, P.Psi hI hmax h𝔭 hd hz u (torsorY hI hmax h𝔭 d hπ l) = 0) : u = 0 := by
  funext i
  set i' := ιk P.hkn i
  have hei : P.e i' ≠ 0 := (P.hsupp i').2 (by simp [i', ιk])
  have hw0 : P.w i' ≠ 0 := by
    intro h0'
    have := P.hw i'
    rw [h0', Nat.cast_zero] at this
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    exact hei ((mul_eq_zero.1 this.symm).resolve_left hdq)
  have hwd : P.w i' ≤ d := by
    have h1 := P.hw i'
    have h2 := P.hle1 i'
    have : (P.w i' : ℚ) ≤ d := by
      rw [h1]; have hdq : (0 : ℚ) ≤ d := by positivity
      nlinarith [P.he i']
    exact_mod_cast this
  -- every element of degree `w` in the ideal generated by generators is killed
  have hkill : ∀ g ∈ ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime P.𝔪)).F (P.w i'),
      ∀ hg : LaurentPolynomial.C g * T (P.w i') ∈
        ReesAlg ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime P.𝔪)),
      P.psiPt hI hmax h𝔭 hd hz u ⟨_, hg⟩ = 0 := by
    intro g hg
    simp only [WFil.loc] at hg
    rw [← span_gensF, Ideal.map_span] at hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      intro hxm
      obtain ⟨g₀, hg₀, rfl⟩ := hx
      obtain ⟨l, hl1, hl2⟩ := exists_index hI hmax h𝔭 (π := π) (j := (P.w i' : ℤ))
        (by have := Nat.pos_of_ne_zero hw0; omega) (by exact_mod_cast hwd) hg₀
      have h1 := h0 l
      rw [LocPres.Psi_apply] at h1
      have : reesMap _ (Localization.AtPrime P.𝔪) (torsorY hI hmax h𝔭 d hπ l) = ⟨_, hxm⟩ := by
        apply Subtype.ext
        rw [reesMap_coe]
        show lmap _ (LaurentPolynomial.C (genCoeff hI hmax h𝔭 d π l) * T (genDeg hI hmax h𝔭 d l)) = _
        rw [lmap_C_mul_T, hl1, hl2]
      rw [this] at h1
      exact h1
    | zero =>
      intro hxm
      have : (⟨LaurentPolynomial.C 0 * T (P.w i'), hxm⟩ :
          ReesAlg ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime P.𝔪))) = 0 :=
        Subtype.ext (by simp)
      rw [this, map_zero]
    | add x y hx hy ihx ihy =>
      intro hxm
      have hx' := C_mul_T_mem_ReesAlg (Φ := (compFil hI hmax h𝔭 d).loc (Localization.AtPrime P.𝔪))
        (j := (P.w i' : ℤ)) (f := x) (by
          simp only [WFil.loc]; rw [← span_gensF, Ideal.map_span]; exact hx)
      have hy' := C_mul_T_mem_ReesAlg (Φ := (compFil hI hmax h𝔭 d).loc (Localization.AtPrime P.𝔪))
        (j := (P.w i' : ℤ)) (f := y) (by
          simp only [WFil.loc]; rw [← span_gensF, Ideal.map_span]; exact hy)
      have : (⟨LaurentPolynomial.C (x + y) * T (P.w i'), hxm⟩ :
          ReesAlg ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime P.𝔪))) = ⟨_, hx'⟩ + ⟨_, hy'⟩ := by
        apply Subtype.ext
        show LaurentPolynomial.C (x + y) * T (P.w i') =
          LaurentPolynomial.C x * T (P.w i') + LaurentPolynomial.C y * T (P.w i')
        rw [map_add, add_mul]
      rw [this, map_add, ihx hx', ihy hy', add_zero]
    | smul b x hx ih =>
      intro hxm
      have hx' := C_mul_T_mem_ReesAlg (Φ := (compFil hI hmax h𝔭 d).loc (Localization.AtPrime P.𝔪))
        (j := (P.w i' : ℤ)) (f := x) (by
          simp only [WFil.loc]; rw [← span_gensF, Ideal.map_span]; exact hx)
      have : (⟨LaurentPolynomial.C (b • x) * T (P.w i'), hxm⟩ :
          ReesAlg ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime P.𝔪))) =
          algebraMap (Localization.AtPrime P.𝔪) _ b * ⟨_, hx'⟩ := by
        apply Subtype.ext
        show LaurentPolynomial.C (b • x) * T (P.w i') =
          algebraMap (Localization.AtPrime P.𝔪) _ b * (LaurentPolynomial.C x * T (P.w i'))
        rw [smul_eq_mul, map_mul, ← LaurentPolynomial.C_eq_algebraMap, mul_assoc]
      rw [this, map_mul, ih hx', mul_zero]
  have hx : P.c.x i' ∈ ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime P.𝔪)).F (P.w i') := by
    rw [P.hF, chartFil]
    have := P.c.x_mem_RF P.e i' hei
    convert this using 2
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    rw [P.hw i']
    field_simp
  have h1 := hkill _ hx (C_mul_T_mem_ReesAlg hx)
  have h2 := P.psiPt_u hI hmax h𝔭 hd hz u i
  have h3 : reesX P.c P.hF P.he hd P.hw (Fin.castSucc (ιk P.hkn i)) = ⟨_, C_mul_T_mem_ReesAlg hx⟩ :=
    Subtype.ext (by rw [reesX_castSucc])
  rw [h3, h1] at h2
  rw [← h2]; rfl

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Jou IsLocalRing MvPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  {z : RealPt A} (hz : ∀ g ∈ 𝔭, z g = 0) (P : LocPres hI hmax h𝔭 (d := d) z)
  {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)

/-- The weighted norm on the fibre coordinates. -/
def LocPres.phi (u : Fin P.k → ℝ) : ℝ :=
  ∑ l, P.Psi hI hmax h𝔭 hd hz u (torsorY hI hmax h𝔭 d hπ l) ^ sphE hI hmax h𝔭 l

lemma LocPres.phi_nonneg (u : Fin P.k → ℝ) : 0 ≤ P.phi hI hmax h𝔭 hd hz hπ u :=
  Finset.sum_nonneg fun l _ => (sphE_even hI hmax h𝔭 l).pow_nonneg _

lemma LocPres.phi_scale (c : ℝ) (u : Fin P.k → ℝ) :
    P.phi hI hmax h𝔭 hd hz hπ (P.scale hI hmax h𝔭 c u) =
      c ^ (2 * d.factorial) * P.phi hI hmax h𝔭 hd hz hπ u := by
  simp only [LocPres.phi, P.Psi_scale_y hI hmax h𝔭 hd hz hπ, mul_pow, ← pow_mul,
    gdeg_mul_sphE hI hmax h𝔭 hd, ← Finset.mul_sum]

lemma LocPres.phi_pos {u : Fin P.k → ℝ} (hu : u ≠ 0) : 0 < P.phi hI hmax h𝔭 hd hz hπ u := by
  rcases (P.phi_nonneg hI hmax h𝔭 hd hz hπ u).lt_or_eq with h | h
  · exact h
  exfalso
  apply hu
  refine P.eq_zero_of_Psi_y hI hmax h𝔭 hd hz hπ u fun l => ?_
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ =>
    (sphE_even hI hmax h𝔭 l).pow_nonneg (P.Psi hI hmax h𝔭 hd hz u (torsorY hI hmax h𝔭 d hπ l)))).1
    h.symm l (Finset.mem_univ l)
  exact pow_eq_zero_iff (sphE_pos hI hmax h𝔭 hd l).ne' |>.1 h0

lemma LocPres.continuous_phi : Continuous (P.phi hI hmax h𝔭 hd hz hπ) :=
  continuous_finset_sum _ fun l _ =>
    ((RealPt.continuous_eval _).comp (P.continuous_Psi hI hmax h𝔭 hd hz)).pow _

/-- The normalizing factor. -/
def LocPres.lam (u : Fin P.k → ℝ) : ℝ :=
  P.phi hI hmax h𝔭 hd hz hπ u ^ (-(((2 * d.factorial : ℕ) : ℝ)⁻¹))

/-- The normalization onto the weighted sphere. -/
def LocPres.nu (u : Fin P.k → ℝ) : Fin P.k → ℝ :=
  P.scale hI hmax h𝔭 (P.lam hI hmax h𝔭 hd hz hπ u) u

lemma LocPres.phi_nu {u : Fin P.k → ℝ} (hu : u ≠ 0) :
    P.phi hI hmax h𝔭 hd hz hπ (P.nu hI hmax h𝔭 hd hz hπ u) = 1 := by
  have hpos := P.phi_pos hI hmax h𝔭 hd hz hπ hu
  rw [LocPres.nu, P.phi_scale, LocPres.lam, Real.rpow_neg hpos.le, inv_pow,
    Real.rpow_inv_natCast_pow hpos.le (by positivity)]
  exact inv_mul_cancel₀ hpos.ne'

lemma LocPres.nu_eq {u : Fin P.k → ℝ} (h : P.phi hI hmax h𝔭 hd hz hπ u = 1) :
    P.nu hI hmax h𝔭 hd hz hπ u = u := by
  funext i
  simp [LocPres.nu, LocPres.lam, h, LocPres.scale]

lemma LocPres.continuousOn_nu : ContinuousOn (P.nu hI hmax h𝔭 hd hz hπ) {u | u ≠ 0} := by
  have hlam : ContinuousOn (P.lam hI hmax h𝔭 hd hz hπ) {u | u ≠ 0} := by
    intro u hu
    refine ContinuousAt.continuousWithinAt ?_
    exact (Real.continuousAt_rpow_const _ _ (Or.inl (P.phi_pos hI hmax h𝔭 hd hz hπ hu).ne')).comp
      (P.continuous_phi hI hmax h𝔭 hd hz hπ).continuousAt
  refine continuousOn_pi.2 fun i => ?_
  exact (hlam.pow _).mul (continuous_apply i).continuousOn

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Jou IsLocalRing MvPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  {z : RealPt A} (hz : ∀ g ∈ 𝔭, z g = 0) (P : LocPres hI hmax h𝔭 (d := d) z)
  {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)

lemma LocPres.Gamma_rel (u : ({0}ᶜ : Set (Fin P.k → ℝ))) :
    ∑ l, P.Psi hI hmax h𝔭 hd hz (P.nu hI hmax h𝔭 hd hz hπ u.1) (torsorY hI hmax h𝔭 d hπ l) ^
        (sphE hI hmax h𝔭 l - 1) *
      (RealPt.toHom (P.Psi hI hmax h𝔭 hd hz (P.nu hI hmax h𝔭 hd hz hπ u.1)))
        (torsorY hI hmax h𝔭 d hπ l) = 1 := by
  rw [← P.phi_nu hI hmax h𝔭 hd hz hπ u.2]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [RealPt.toHom_apply, ← pow_succ, Nat.sub_add_cancel (sphE_pos hI hmax h𝔭 hd l)]

/-- **The fibre over `z ∈ V(𝔭)` as a continuous image of `ℝ^k ∖ {0}`.** -/
def LocPres.Gamma (u : ({0}ᶜ : Set (Fin P.k → ℝ))) : RealPt (Torsor hI hmax h𝔭 d hπ) :=
  jPt (torsorY hI hmax h𝔭 d hπ) (RealPt.toHom (P.Psi hI hmax h𝔭 hd hz (P.nu hI hmax h𝔭 hd hz hπ u.1)))
    (fun l => P.Psi hI hmax h𝔭 hd hz (P.nu hI hmax h𝔭 hd hz hπ u.1) (torsorY hI hmax h𝔭 d hπ l) ^
      (sphE hI hmax h𝔭 l - 1)) (P.Gamma_rel hI hmax h𝔭 hd hz hπ u)

lemma LocPres.Gamma_algebraMap (u : ({0}ᶜ : Set (Fin P.k → ℝ))) (r : ReesAlg (compFil hI hmax h𝔭 d)) :
    P.Gamma hI hmax h𝔭 hd hz hπ u (algebraMap _ (Torsor hI hmax h𝔭 d hπ) r) =
      P.Psi hI hmax h𝔭 hd hz (P.nu hI hmax h𝔭 hd hz hπ u.1) r :=
  jPt_algebraMap _ _ _ _ r

lemma LocPres.Gamma_σ (u : ({0}ᶜ : Set (Fin P.k → ℝ))) (l) :
    P.Gamma hI hmax h𝔭 hd hz hπ u (σ (torsorY hI hmax h𝔭 d hπ) l) =
      P.Psi hI hmax h𝔭 hd hz (P.nu hI hmax h𝔭 hd hz hπ u.1) (torsorY hI hmax h𝔭 d hπ l) ^
        (sphE hI hmax h𝔭 l - 1) :=
  jPt_σ _ _ _ _ l

lemma LocPres.continuous_Gamma : Continuous (P.Gamma hI hmax h𝔭 hd hz hπ) := by
  have hnu : Continuous fun u : ({0}ᶜ : Set (Fin P.k → ℝ)) => P.nu hI hmax h𝔭 hd hz hπ u.1 :=
    (P.continuousOn_nu hI hmax h𝔭 hd hz hπ).comp_continuous continuous_subtype_val
      (fun u => u.2)
  have hPsi := (P.continuous_Psi hI hmax h𝔭 hd hz).comp hnu
  refine continuous_jPt _ _ (fun a => (RealPt.continuous_eval a).comp hPsi) _
    (fun l => ((RealPt.continuous_eval _).comp hPsi).pow _) _

lemma LocPres.Gamma_comap (u : ({0}ᶜ : Set (Fin P.k → ℝ))) :
    RealPt.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) (P.Gamma hI hmax h𝔭 hd hz hπ u) = z := by
  ext a
  rw [RealPt.comap_apply, IsScalarTower.algebraMap_apply A (ReesAlg (compFil hI hmax h𝔭 d)),
    P.Gamma_algebraMap, P.Psi_algebraMap]

lemma LocPres.Gamma_mem {K : Set (RealPt A)} (hzK : z ∈ K) (u : ({0}ᶜ : Set (Fin P.k → ℝ))) :
    P.Gamma hI hmax h𝔭 hd hz hπ u ∈ torsorK hI hmax h𝔭 hπ K := by
  refine ⟨by rw [P.Gamma_comap]; exact hzK, ?_, ?_, fun l => ?_⟩
  · rw [torsorS, P.Gamma_algebraMap, P.Psi_s]
  · refine (Finset.sum_congr rfl fun l _ => ?_).trans (P.phi_nu hI hmax h𝔭 hd hz hπ u.2)
    rw [yU, P.Gamma_algebraMap]
  · rw [P.Gamma_σ, yU, P.Gamma_algebraMap]

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Jou IsLocalRing MvPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)

include hd hw hπ in
lemma genCoeff_mem_p (l : Fin (nGen hI hmax h𝔭 d + 1)) : genCoeff hI hmax h𝔭 d π l ∈ 𝔭 := by
  have h1 := genCoeff_mem hI hmax h𝔭 d hπ l
  rw [compFil_F] at h1
  have hj := genDeg_pos hI hmax h𝔭 d l
  have h2 : compF I 𝔭 ((genDeg hI hmax h𝔭 d l : ℚ) / d) ≤ compF I 𝔭 (1 / d) := by
    refine compF_antitone ?_ hI (fun 𝔪 _ h𝔭𝔪' => ?_)
    · have : (1 : ℚ) ≤ genDeg hI hmax h𝔭 d l := by exact_mod_cast hj
      have hd' : (0 : ℚ) < d := by exact_mod_cast hd
      exact div_le_div_of_nonneg_right this hd'.le
    · have hZ := mem_maxLocus_of_minimal hI hmax h𝔭 𝔪 h𝔭𝔪'
      exact ⟨hZ.1, v₀, hZ.2⟩
  rw [compF_one_div hI hmax h𝔭 hd hw] at h2
  exact h2 h1

/-- The fibre of the compact set over a real point of the base. -/
def torsorFib (K : Set (RealPt A)) (z : RealPt A) : Set (RealPt (Torsor hI hmax h𝔭 d hπ)) :=
  {w | w ∈ torsorK hI hmax h𝔭 hπ K ∧ RealPt.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) w = z}

variable {z : RealPt A} (hz : ∀ g ∈ 𝔭, z g = 0) (P : LocPres hI hmax h𝔭 (d := d) z)

include hw in
theorem LocPres.fib_eq {K : Set (RealPt A)} (hzK : z ∈ K) :
    torsorFib hI hmax h𝔭 hπ K z = Set.range (P.Gamma hI hmax h𝔭 hd hz hπ) := by
  ext w
  constructor
  · rintro ⟨hwK, hwz⟩
    have hs := s_pow_eq hI hmax h𝔭 hd hπ w hwK.2.2.1
    have hsum0 : ∑ l, w (algebraMap A (Torsor hI hmax h𝔭 d hπ) (genCoeff hI hmax h𝔭 d π l)) ^
        sphE hI hmax h𝔭 l = 0 := Finset.sum_eq_zero fun l _ => by
      have : w (algebraMap A (Torsor hI hmax h𝔭 d hπ) (genCoeff hI hmax h𝔭 d π l)) =
          z (genCoeff hI hmax h𝔭 d π l) := by rw [← hwz]; rfl
      rw [this, hz _ (genCoeff_mem_p hI hmax h𝔭 hd hw hπ l), zero_pow (sphE_pos hI hmax h𝔭 hd l).ne']
    rw [hsum0] at hs
    have hs0 : w (torsorS hI hmax h𝔭 hπ) = 0 := (pow_eq_zero_iff (by positivity)).1 hs
    set wR := RealPt.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ)) w
    obtain ⟨u₀, hu₀⟩ := P.eq_Psi hI hmax h𝔭 hd hz wR (fun a => by
      rw [← hwz]
      simp only [wR, RealPt.comap_apply]
      rw [← IsScalarTower.algebraMap_apply]) hs0
    have hphi : P.phi hI hmax h𝔭 hd hz hπ u₀ = 1 := by
      rw [← hwK.2.2.1]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← hu₀]; rfl
    have hne : u₀ ≠ 0 := by
      rintro rfl
      have h0 : P.phi hI hmax h𝔭 hd hz hπ 0 = 0 := by
        have := P.phi_scale hI hmax h𝔭 hd hz hπ 0 0
        have hs0' : P.scale hI hmax h𝔭 0 0 = 0 := by funext i; simp [LocPres.scale]
        rw [hs0', zero_pow (by positivity), zero_mul] at this
        exact this
      rw [h0] at hphi
      exact zero_ne_one hphi
    refine ⟨⟨u₀, hne⟩, ?_⟩
    have hnu := P.nu_eq hI hmax h𝔭 hd hz hπ hphi
    apply realPt_J_ext
    · intro r
      rw [P.Gamma_algebraMap, hnu, ← hu₀]; rfl
    · intro l
      rw [P.Gamma_σ, hnu, hwK.2.2.2 l, ← hu₀]; rfl
  · rintro ⟨u, rfl⟩
    exact ⟨P.Gamma_mem hI hmax h𝔭 hd hz hπ hzK u, P.Gamma_comap hI hmax h𝔭 hd hz hπ u⟩

include hd hw hz in
theorem fib_connected (hk2 : v₀ 1 ≠ 0) {K : Set (RealPt A)} (hzK : z ∈ K) :
    IsConnected (torsorFib hI hmax h𝔭 hπ K z) := by
  obtain ⟨P⟩ := LocPres.nonempty hI hmax h𝔭 hw z hz
  rw [P.fib_eq hI hmax h𝔭 hd hw hπ hz hzK]
  haveI : ConnectedSpace ({0}ᶜ : Set (Fin P.k → ℝ)) :=
    isConnected_iff_connectedSpace.1 (isConnected_compl_singleton_of_one_lt_rank (by
      rw [rank_fin_fun]; exact_mod_cast (P.hk2 hk2 : 2 ≤ P.k)) 0)
  exact isConnected_range (P.continuous_Gamma hI hmax h𝔭 hd hz hπ)

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Jou IsLocalRing MvPolynomial Topology

/-- Connectedness of a fibre of a restricted map, via the ambient fibre. -/
lemma isConnected_restrict_fiber {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {K' : Set X} {K : Set Y} (h : Set.MapsTo f K' K) (y : K)
    (hc : IsConnected {w | w ∈ K' ∧ f w = y}) :
    IsConnected ((h.restrict f K' K) ⁻¹' {y}) := by
  have himg : Subtype.val '' ((h.restrict f K' K) ⁻¹' {y}) = {w | w ∈ K' ∧ f w = y} := by
    ext w
    constructor
    · rintro ⟨⟨w, hw⟩, hy, rfl⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy
      exact ⟨hw, congrArg Subtype.val hy⟩
    · rintro ⟨hw, hy⟩
      exact ⟨⟨w, hw⟩, Subtype.ext hy, rfl⟩
  rw [← himg] at hc
  exact ⟨(Set.image_nonempty.1 hc.1), IsInducing.subtypeVal.isPreconnected_image.1 hc.2⟩

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)

include hd hw hπ in
lemma kills_of_gNorm_zero {z : RealPt A} (h0 : gNorm hI hmax h𝔭 d π z = 0) : ∀ g ∈ 𝔭, z g = 0 := by
  have hl : ∀ l, z (genCoeff hI hmax h𝔭 d π l) = 0 := fun l => by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ =>
      (sphE_even hI hmax h𝔭 l).pow_nonneg (z (genCoeff hI hmax h𝔭 d π l)))).1 h0 l
      (Finset.mem_univ l)
    exact (pow_eq_zero_iff (sphE_pos hI hmax h𝔭 hd l).ne').1 this
  have hle : 𝔭 ≤ RingHom.ker (RealPt.toHom z) := by
    rw [← compF_one_div hI hmax h𝔭 hd hw, show (1 : ℚ) / d = ((1 : ℤ) : ℚ) / d by push_cast; ring,
      ← compFil_F hI hmax h𝔭 d 1, ← span_gensF hI hmax h𝔭 d 1, Ideal.span_le]
    intro g hg
    obtain ⟨l, -, hl2⟩ := exists_index hI hmax h𝔭 (π := π) le_rfl (by exact_mod_cast hd) hg
    rw [SetLike.mem_coe, RingHom.mem_ker, ← hl2]
    exact hl l
  exact fun g hg => hle hg

/-- **Real points of the torsor**: the weighted sphere bundle is compact and maps onto `K` with
connected fibres. -/
theorem torsorRealPts : TorsorRealPts := by
  intro A _ _ _ _ _ I hI v₀ hmax 𝔭 h𝔭 d hd hw π hπ hπ0 hk2 K hK
  refine ⟨torsorK hI hmax h𝔭 hπ K, torsorK_isCompact hI hmax h𝔭 hd hw hπ hK, ?_⟩
  have hmaps : Set.MapsTo (RealPt.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)))
      (torsorK hI hmax h𝔭 hπ K) K := fun w hw => hw.1
  refine ⟨hmaps, ⟨?_, ?_, ?_⟩⟩
  · exact ((RealPt.continuous_comap _).comp continuous_subtype_val).subtype_mk _
  · rintro ⟨z, hzK⟩
    rcases (gNorm_nonneg hI hmax h𝔭 (d := d) (π := π) z).lt_or_eq with hpos | h0
    · exact ⟨⟨ptA hI hmax h𝔭 hd hπ z hpos, ptA_mem hI hmax h𝔭 hd hπ K hzK hpos⟩,
        Subtype.ext (ptA_comap hI hmax h𝔭 hd hπ z hpos)⟩
    · have hz := kills_of_gNorm_zero hI hmax h𝔭 hd hw hπ h0.symm
      obtain ⟨P⟩ := LocPres.nonempty hI hmax h𝔭 hw z hz
      have hk : 0 < P.k := by have := P.hk2 hk2; omega
      set u : ({0}ᶜ : Set (Fin P.k → ℝ)) := ⟨fun _ => 1, fun h => by
        have := congrFun h ⟨0, hk⟩; simp at this⟩
      exact ⟨⟨P.Gamma hI hmax h𝔭 hd hz hπ u, P.Gamma_mem hI hmax h𝔭 hd hz hπ hzK u⟩,
        Subtype.ext (P.Gamma_comap hI hmax h𝔭 hd hz hπ u)⟩
  · rintro ⟨z, hzK⟩
    apply isConnected_restrict_fiber
    show IsConnected (torsorFib hI hmax h𝔭 hπ K z)
    rcases (gNorm_nonneg hI hmax h𝔭 (d := d) (π := π) z).lt_or_eq with hpos | h0
    · have : torsorFib hI hmax h𝔭 hπ K z = {ptA hI hmax h𝔭 hd hπ z hpos} := by
        ext w
        constructor
        · rintro ⟨hwK, hwz⟩
          exact eq_ptA hI hmax h𝔭 hd hπ K hwK hwz hpos
        · rintro rfl
          exact ⟨ptA_mem hI hmax h𝔭 hd hπ K hzK hpos, ptA_comap hI hmax h𝔭 hd hπ z hpos⟩
      rw [this]
      exact isConnected_singleton
    · exact fib_connected hI hmax h𝔭 hd hw hπ (kills_of_gNorm_zero hI hmax h𝔭 hd hw hπ h0.symm)
        hk2 hzK

end BezoutCounterexample.Principalization

namespace BezoutCounterexample.Principalization

/-- **Proposition 4.6** (`PrincipalizationExtension`): every nonzero ideal of a smooth factorial
`ℚ`-domain becomes principal in a tower of smooth factorial domains, with a monotone surjection of
compact sets of real points. -/
theorem principalizationExtension : PrincipalizationExtension :=
  principalizationExtension_of torsorRealPts

end BezoutCounterexample.Principalization

