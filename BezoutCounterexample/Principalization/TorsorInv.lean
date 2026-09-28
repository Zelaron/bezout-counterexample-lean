import BezoutCounterexample.Principalization.Torsor

/-!
# Invariants and components on the torsor

Lemma 4.3 (`lem:torsor-invariant`) of the paper.

* `IsInv.transfer_mvLoc`, `IsInv.transfer_polyLoc`: smooth invariance for localizations of
  polynomial rings.
* `invAt_rees_of_base` (`B_𝔮 → R_P` off `V(s)`) and `invAt_torsor_of_rees` (`R_P → U_Q`).
* `torsor_invAt`: at points of `V(I_w U)` the invariant either increases (on `V(s)`) or equals the
  invariant of `I` at a point of `V(I) ∖ V(𝔭)`.
* `torsor_comp_isPrime`, `torsor_count`: the other components stay prime and the number of
  components of the maximal locus drops.
-/

noncomputable section



namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

section UnitPre

variable {W S' : Type*} [CommRing W] [CommRing S'] (θ : W →+* S')

/-- The elements whose image is a unit. -/
def unitPre : Submonoid W := (IsUnit.submonoid S').comap θ

lemma mem_unitPre {w : W} : w ∈ unitPre θ ↔ IsUnit (θ w) := IsUnit.mem_submonoid_iff _

/-- An injective map such that every element is a fraction is a localization. -/
lemma isLocalization_unitPre (hinj : Function.Injective θ)
    (hsurj : ∀ z : S', ∃ a b : W, IsUnit (θ b) ∧ z * θ b = θ a) :
    @IsLocalization _ _ (unitPre θ) S' _ θ.toAlgebra := by
  let := θ.toAlgebra
  refine ⟨fun m => (mem_unitPre θ).1 m.2, fun z => ?_, fun {x y} h => ⟨1, by
    simp only [OneMemClass.coe_one, one_mul]; exact hinj h⟩⟩
  obtain ⟨a, b, hb, h⟩ := hsurj z
  exact ⟨⟨a, ⟨b, (mem_unitPre θ).2 hb⟩⟩, h⟩

end UnitPre

section SILoc

variable {S S' : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] [IsNoetherianRing S]
  [CommRing S'] [Algebra ℚ S'] [IsLocalRing S'] [IsNoetherianRing S']
  [Algebra.FormallySmooth ℚ S'] [Algebra.FormallySmooth ℚ (ResidueField S')]
  [Algebra.IsIntegral ℚ (ResidueField S')] {n : ℕ}

/-- **Smooth invariance** for a target which is a localization of `S[X₁, …, X_r]`. -/
theorem IsInv.transfer_mvLoc {r : ℕ} (θ : MvPolynomial (Fin r) S →+* S')
    (hinj : Function.Injective θ) (hsurj : ∀ z : S', ∃ a b, IsUnit (θ b) ∧ z * θ b = θ a)
    (hloc : ∀ a ∈ maximalIdeal S, θ (MvPolynomial.C a) ∈ maximalIdeal S')
    {c : Chart S n} (hc : c.IsCentred) {I : Ideal S} (hI : I ≠ ⊥) (hIm : I ≤ maximalIdeal S)
    {e : Fin n → ℚ} (he : IsInv I n e) :
    IsInv (I.map (θ.comp MvPolynomial.C)) (n + r) (pad (n + r) e) := by
  let := θ.toAlgebra
  have : IsScalarTower ℚ (MvPolynomial (Fin r) S) S' :=
    IsScalarTower.of_algebraMap_eq (fun q => (RingHom.map_rat_algebraMap θ q).symm)
  have := isLocalization_unitPre θ hinj hsurj
  have hcc := (c.compat_mvPolynomial r).trans
    ((c.mvPolynomial r).compat_localization (L := S') (unitPre θ))
  exact IsInv.transfer (fun a ha => hloc a ha) hc hcc hI hIm he

/-- **Smooth invariance** for a target which is a localization of `S[X]`. -/
theorem IsInv.transfer_polyLoc (θ : Polynomial S →+* S')
    (hinj : Function.Injective θ) (hsurj : ∀ z : S', ∃ a b, IsUnit (θ b) ∧ z * θ b = θ a)
    (hloc : ∀ a ∈ maximalIdeal S, θ (Polynomial.C a) ∈ maximalIdeal S')
    {c : Chart S n} (hc : c.IsCentred) {I : Ideal S} (hI : I ≠ ⊥) (hIm : I ≤ maximalIdeal S)
    {e : Fin n → ℚ} (he : IsInv I n e) :
    IsInv (I.map (θ.comp Polynomial.C)) (n + 1) (pad (n + 1) e) := by
  let := θ.toAlgebra
  have : IsScalarTower ℚ (Polynomial S) S' :=
    IsScalarTower.of_algebraMap_eq (fun q => (RingHom.map_rat_algebraMap θ q).symm)
  have := isLocalization_unitPre θ hinj hsurj
  have hcc := c.compat_polynomial.trans (c.polynomial.compat_localization (L := S') (unitPre θ))
  exact IsInv.transfer (fun a ha => hloc a ha) hc hcc hI hIm he

end SILoc

section ChartLoc

variable {S S' : Type*} [CommRing S] [Algebra ℚ S] [CommRing S'] [Algebra ℚ S'] {n : ℕ}

lemma chart_of_mvLoc {r : ℕ} (θ : MvPolynomial (Fin r) S →+* S')
    (hinj : Function.Injective θ) (hsurj : ∀ z : S', ∃ a b, IsUnit (θ b) ∧ z * θ b = θ a)
    (c : Chart S n) : Nonempty (Chart S' (n + r)) := by
  let := θ.toAlgebra
  have : IsScalarTower ℚ (MvPolynomial (Fin r) S) S' :=
    IsScalarTower.of_algebraMap_eq (fun q => (RingHom.map_rat_algebraMap θ q).symm)
  have := isLocalization_unitPre θ hinj hsurj
  exact ⟨(c.mvPolynomial r).localization (unitPre θ)⟩

lemma chart_of_polyLoc (θ : Polynomial S →+* S')
    (hinj : Function.Injective θ) (hsurj : ∀ z : S', ∃ a b, IsUnit (θ b) ∧ z * θ b = θ a)
    (c : Chart S n) : Nonempty (Chart S' (n + 1)) := by
  let := θ.toAlgebra
  have : IsScalarTower ℚ (Polynomial S) S' :=
    IsScalarTower.of_algebraMap_eq (fun q => (RingHom.map_rat_algebraMap θ q).symm)
  have := isLocalization_unitPre θ hinj hsurj
  exact ⟨c.polynomial.localization (unitPre θ)⟩

end ChartLoc

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

section E1

variable {B : Type*} [CommRing B] [Algebra ℚ B] [IsDomain B] (Φ : WFil B)
  (hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤)
  (P : Ideal (ReesAlg Φ)) [P.IsPrime] (hsP : reesS Φ hneg ∉ P)
include hneg hsP

omit [IsDomain B] [Algebra ℚ B] in
lemma s_isUnit_loc : IsUnit (algebraMap (ReesAlg Φ) (Localization.AtPrime P) (reesS Φ hneg)) :=
  IsLocalization.map_units (Localization.AtPrime P) (⟨reesS Φ hneg, hsP⟩ : P.primeCompl)

/-- The map `B[T^±] → R_P` (inverting `s`). -/
def laurentToLoc : B[T;T⁻¹] →+* Localization.AtPrime P := by
  haveI := isLocalization_away_s Φ hneg
  exact IsLocalization.Away.lift (reesS Φ hneg) (s_isUnit_loc Φ hneg P hsP)

omit [IsDomain B] [Algebra ℚ B] in
lemma laurentToLoc_coe (r : ReesAlg Φ) :
    laurentToLoc Φ hneg P hsP (r : B[T;T⁻¹]) = algebraMap (ReesAlg Φ) (Localization.AtPrime P) r := by
  have := isLocalization_away_s Φ hneg
  exact IsLocalization.lift_eq (M := Submonoid.powers (reesS Φ hneg)) _ r

omit [Algebra ℚ B] in
lemma laurentToLoc_injective : Function.Injective (laurentToLoc Φ hneg P hsP) := by
  have := isLocalization_away_s Φ hneg
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨r, m⟩, hr⟩ := IsLocalization.surj (Submonoid.powers (reesS Φ hneg)) z
  have hr' : z * (m : B[T;T⁻¹]) = (r : B[T;T⁻¹]) := hr
  have h1 : algebraMap (ReesAlg Φ) (Localization.AtPrime P) r = 0 := by
    rw [← laurentToLoc_coe Φ hneg P hsP, ← hr', map_mul, hz, zero_mul]
  have h2 : r = 0 := IsLocalization.injective (Localization.AtPrime P)
    (Ideal.primeCompl_le_nonZeroDivisors P) (h1.trans (map_zero _).symm)
  have hm : IsUnit (algebraMap (ReesAlg Φ) B[T;T⁻¹] m) := IsLocalization.map_units _ m
  rw [h2] at hr
  rw [map_zero] at hr
  exact hm.mul_left_eq_zero.1 hr

variable (𝔮 : Ideal B) [𝔮.IsPrime] (h𝔮 : 𝔮 = P.comap (algebraMap B (ReesAlg Φ)))

/-- The map `B_𝔮[X] → R_P`, `X ↦ T`. -/
def theta1 : Polynomial (Localization.AtPrime 𝔮) →+* Localization.AtPrime P :=
  Polynomial.eval₂RingHom (Localization.localRingHom 𝔮 P (algebraMap B (ReesAlg Φ)) h𝔮)
    (laurentToLoc Φ hneg P hsP (T 1))

omit [IsDomain B] [Algebra ℚ B] in
lemma theta1_C (a : Localization.AtPrime 𝔮) :
    theta1 Φ hneg P hsP 𝔮 h𝔮 (Polynomial.C a) =
      Localization.localRingHom 𝔮 P (algebraMap B (ReesAlg Φ)) h𝔮 a := by
  simp [theta1]

omit [IsDomain B] [Algebra ℚ B] in
lemma theta1_X : theta1 Φ hneg P hsP 𝔮 h𝔮 Polynomial.X = laurentToLoc Φ hneg P hsP (T 1) := by
  simp [theta1]

omit [IsDomain B] [Algebra ℚ B] in
lemma theta1_map (q : Polynomial B) :
    theta1 Φ hneg P hsP 𝔮 h𝔮 (q.map (algebraMap B (Localization.AtPrime 𝔮))) =
      laurentToLoc Φ hneg P hsP (Polynomial.toLaurent q) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add, map_add, hp, hq, map_add, map_add]
  | monomial k b =>
    rw [Polynomial.map_monomial, Polynomial.toLaurent_C_mul_T, ← Polynomial.C_mul_X_pow_eq_monomial,
      map_mul, map_pow, theta1_C, theta1_X, Localization.localRingHom_to_map, map_mul]
    have hT : (T (k : ℤ) : B[T;T⁻¹]) = T 1 ^ k := by rw [T_pow, mul_one]
    rw [hT, map_pow]
    congr 1
    rw [← laurentToLoc_coe Φ hneg P hsP]
    congr 1

end E1

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

section E1b

variable {B : Type*} [CommRing B] [Algebra ℚ B] [IsDomain B] (Φ : WFil B)
  (hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤)
  (P : Ideal (ReesAlg Φ)) [P.IsPrime] (hsP : reesS Φ hneg ∉ P)
  (𝔮 : Ideal B) [𝔮.IsPrime] (h𝔮 : 𝔮 = P.comap (algebraMap B (ReesAlg Φ)))
include hneg hsP h𝔮

omit [Algebra ℚ B] in
lemma theta1_injective : Function.Injective (theta1 Φ hneg P hsP 𝔮 h𝔮) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec 𝔮.primeCompl w
  have hsm : ∀ p : Polynomial (Localization.AtPrime 𝔮), b • p =
      Polynomial.C (algebraMap B (Localization.AtPrime 𝔮) b) * p := fun p => by
    rw [Algebra.smul_def, Polynomial.algebraMap_apply]
  have h1 : theta1 Φ hneg P hsP 𝔮 h𝔮
      ((integerNormalization 𝔮.primeCompl w).map (algebraMap B _)) = 0 := by
    rw [hb, hsm, map_mul, hw, mul_zero]
  rw [theta1_map] at h1
  have h2 := laurentToLoc_injective Φ hneg P hsP (h1.trans (map_zero _).symm)
  have h3 : integerNormalization 𝔮.primeCompl w = 0 :=
    Polynomial.toLaurent_injective (h2.trans (map_zero _).symm)
  exact (IsLocalization.integerNormalization_eq_zero_iff
    (Ideal.primeCompl_le_nonZeroDivisors 𝔮) w).1 h3

omit [IsDomain B] [Algebra ℚ B] in
lemma theta1_surj (z : Localization.AtPrime P) :
    ∃ a b, IsUnit (theta1 Φ hneg P hsP 𝔮 h𝔮 b) ∧
      z * theta1 Φ hneg P hsP 𝔮 h𝔮 b = theta1 Φ hneg P hsP 𝔮 h𝔮 a := by
  obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl z
  obtain ⟨N, qr, hqr⟩ := LaurentPolynomial.exists_T_pow (r : B[T;T⁻¹])
  obtain ⟨N', qt, hqt⟩ := LaurentPolynomial.exists_T_pow ((t : ReesAlg Φ) : B[T;T⁻¹])
  set θ := theta1 Φ hneg P hsP 𝔮 h𝔮
  set L := laurentToLoc Φ hneg P hsP
  have hX : ∀ n : ℕ, θ (Polynomial.X ^ n) = L (T n) := by
    intro n; rw [map_pow, theta1_X, ← map_pow, T_pow, mul_one]
  have hr : θ (qr.map (algebraMap B _)) = algebraMap _ (Localization.AtPrime P) r * L (T N) := by
    rw [theta1_map, hqr, map_mul, laurentToLoc_coe]
  have ht : θ (qt.map (algebraMap B _)) =
      algebraMap _ (Localization.AtPrime P) (t : ReesAlg Φ) * L (T N') := by
    rw [theta1_map, hqt, map_mul, laurentToLoc_coe]
  have hLu : ∀ m : ℤ, IsUnit (L (T m)) := fun m => (isUnit_T m).map L
  refine ⟨qr.map (algebraMap B _) * Polynomial.X ^ N', Polynomial.X ^ N * qt.map (algebraMap B _),
    ?_, ?_⟩
  · rw [map_mul, hX, ht]
    exact (hLu _).mul ((IsLocalization.map_units _ t).mul (hLu _))
  · rw [map_mul, map_mul, hX, hX, hr, ht]
    have hs := IsLocalization.mk'_spec (Localization.AtPrime P) r t
    calc IsLocalization.mk' (Localization.AtPrime P) r t * (L (T N) *
          (algebraMap _ (Localization.AtPrime P) (t : ReesAlg Φ) * L (T N'))) =
        (IsLocalization.mk' (Localization.AtPrime P) r t *
          algebraMap _ (Localization.AtPrime P) (t : ReesAlg Φ)) * (L (T N) * L (T N')) := by ring
      _ = _ := by rw [hs]; ring

omit [IsDomain B] [Algebra ℚ B] in
lemma theta1_local (a : Localization.AtPrime 𝔮) (ha : a ∈ maximalIdeal (Localization.AtPrime 𝔮)) :
    theta1 Φ hneg P hsP 𝔮 h𝔮 (Polynomial.C a) ∈ maximalIdeal (Localization.AtPrime P) := by
  rw [theta1_C]
  exact fun h => ha (isUnit_of_map_unit _ a h)

end E1b

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

section E2

variable {R : Type*} [CommRing R] [IsDomain R] {r : ℕ} (y : Fin (r + 1) → R)
  [IsDomain (Jou.J y)] (Q : Ideal (Jou.J y)) [Q.IsPrime] {l : Fin (r + 1)}
  (hyl : y l ∉ Q.comap (algebraMap R (Jou.J y)))

local notation "PP" => Q.comap (algebraMap R (Jou.J y))

/-- The base change `J(y) → J(y_P)`. -/
abbrev jmap : Jou.J y →+* Jou.J (algebraMap R (Localization.AtPrime PP) ∘ y) :=
  Jou.map (algebraMap R (Localization.AtPrime PP)) y

omit [IsDomain R] [IsDomain (Jou.J y)] in
lemma jmap_isLocalization :
    @IsLocalization _ _ ((PP).primeCompl.map (algebraMap R (Jou.J y)))
      (Jou.J (algebraMap R (Localization.AtPrime PP) ∘ y)) _ (jmap y Q).toAlgebra :=
  Jou.isLocalization_map y (PP).primeCompl

include hyl

/-- The unit `y_l` of `R_P`. -/
def ylUnit : (Localization.AtPrime PP)ˣ :=
  (IsLocalization.map_units (Localization.AtPrime PP) (⟨y l, hyl⟩ : (PP).primeCompl)).unit

/-- `J(y_P) ≅ R_P[X]`. -/
def jequiv : Jou.J (algebraMap R (Localization.AtPrime PP) ∘ y) ≃+*
    MvPolynomial (Fin r) (Localization.AtPrime PP) :=
  Jou.equivPoly (c := algebraMap R (Localization.AtPrime PP) ∘ y) (l := l) (ylUnit y Q hyl) rfl

omit hyl in
omit [IsDomain R] [IsDomain (Jou.J y)] in
lemma jmap_units (m : (PP).primeCompl.map (algebraMap R (Jou.J y))) :
    IsUnit (algebraMap (Jou.J y) (Localization.AtPrime Q) m) := by
  obtain ⟨_, ⟨a, ha, rfl⟩⟩ := m
  exact IsLocalization.map_units (Localization.AtPrime Q) (⟨algebraMap R (Jou.J y) a, ha⟩ : Q.primeCompl)

/-- The map `J(y_P) → U_Q`. -/
def jlift : Jou.J (algebraMap R (Localization.AtPrime PP) ∘ y) →+* Localization.AtPrime Q := by
  letI := (jmap y Q).toAlgebra
  haveI := jmap_isLocalization y Q
  exact IsLocalization.lift (M := (PP).primeCompl.map (algebraMap R (Jou.J y)))
    (S := Jou.J (algebraMap R (Localization.AtPrime PP) ∘ y)) (jmap_units y Q)

omit hyl [IsDomain R] [IsDomain (Jou.J y)] in
lemma jlift_jmap (u : Jou.J y) :
    jlift y Q (jmap y Q u) = algebraMap (Jou.J y) (Localization.AtPrime Q) u := by
  let := (jmap y Q).toAlgebra
  have := jmap_isLocalization y Q
  exact IsLocalization.lift_eq (M := (PP).primeCompl.map (algebraMap R (Jou.J y)))
    (S := Jou.J (algebraMap R (Localization.AtPrime PP) ∘ y)) (jmap_units y Q) u

end E2

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

section E2b

variable {R : Type*} [CommRing R] [IsDomain R] {r : ℕ} (y : Fin (r + 1) → R)
  [IsDomain (Jou.J y)] (Q : Ideal (Jou.J y)) [Q.IsPrime] {l : Fin (r + 1)}
  (hyl : y l ∉ Q.comap (algebraMap R (Jou.J y)))
include hyl

local notation "PP" => Q.comap (algebraMap R (Jou.J y))

/-- The map `R_P[X] → U_Q`. -/
def theta2 : MvPolynomial (Fin r) (Localization.AtPrime PP) →+* Localization.AtPrime Q :=
  (jlift y Q).comp (jequiv y Q hyl).symm.toRingHom

omit [IsDomain R] [IsDomain (Jou.J y)] in
lemma theta2_jequiv (z : Jou.J (algebraMap R (Localization.AtPrime PP) ∘ y)) :
    theta2 y Q hyl (jequiv y Q hyl z) = jlift y Q z := by
  simp [theta2]

omit [IsDomain R] [IsDomain (Jou.J y)] in
lemma jequiv_algebraMap (b : Localization.AtPrime PP) :
    jequiv y Q hyl (algebraMap _ _ b) = MvPolynomial.C b :=
  Jou.equivPoly_algebraMap _ _ b

omit [IsDomain R] [IsDomain (Jou.J y)] in
lemma theta2_C_algebraMap (a : R) :
    theta2 y Q hyl (MvPolynomial.C (algebraMap R (Localization.AtPrime PP) a)) =
      algebraMap (Jou.J y) (Localization.AtPrime Q) (algebraMap R (Jou.J y) a) := by
  have h1 : MvPolynomial.C (algebraMap R (Localization.AtPrime PP) a) =
      jequiv y Q hyl (jmap y Q (algebraMap R (Jou.J y) a)) := by
    rw [jmap, Jou.map_algebraMap, jequiv_algebraMap]
  rw [h1, theta2_jequiv, jlift_jmap]

omit [IsDomain R] [IsDomain (Jou.J y)] in
lemma theta2_comp :
    (theta2 y Q hyl).comp (MvPolynomial.C.comp (algebraMap R (Localization.AtPrime PP))) =
      (algebraMap (Jou.J y) (Localization.AtPrime Q)).comp (algebraMap R (Jou.J y)) :=
  RingHom.ext fun a => theta2_C_algebraMap y Q hyl a

omit [IsDomain R] in
lemma theta2_injective : Function.Injective (theta2 y Q hyl) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  let := (jmap y Q).toAlgebra
  have := jmap_isLocalization y Q
  obtain ⟨⟨u, m⟩, hum⟩ := IsLocalization.surj ((PP).primeCompl.map (algebraMap R (Jou.J y)))
    ((jequiv y Q hyl).symm w)
  have hw' : jlift y Q ((jequiv y Q hyl).symm w) = 0 := hw
  have h1 : algebraMap (Jou.J y) (Localization.AtPrime Q) u = 0 := by
    rw [← jlift_jmap, ← show algebraMap (Jou.J y) _ u = jmap y Q u from rfl, ← hum, map_mul, hw',
      zero_mul]
  have h2 : u = 0 := IsLocalization.injective (Localization.AtPrime Q)
    (Ideal.primeCompl_le_nonZeroDivisors Q) (h1.trans (map_zero _).symm)
  rw [h2, map_zero] at hum
  have hmu : IsUnit (algebraMap (Jou.J y) (Jou.J (algebraMap R (Localization.AtPrime PP) ∘ y)) m) :=
    IsLocalization.map_units _ m
  have h3 : (jequiv y Q hyl).symm w = 0 := hmu.mul_left_eq_zero.1 hum
  simpa using congrArg (jequiv y Q hyl) h3

omit [IsDomain R] [IsDomain (Jou.J y)] in
lemma theta2_surj (z : Localization.AtPrime Q) :
    ∃ a b, IsUnit (theta2 y Q hyl b) ∧ z * theta2 y Q hyl b = theta2 y Q hyl a := by
  obtain ⟨⟨u, t⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl z
  refine ⟨jequiv y Q hyl (jmap y Q u), jequiv y Q hyl (jmap y Q t), ?_, ?_⟩
  · rw [theta2_jequiv, jlift_jmap]; exact IsLocalization.map_units _ t
  · rw [theta2_jequiv, theta2_jequiv, jlift_jmap, jlift_jmap]
    exact IsLocalization.mk'_spec _ u t

omit [IsDomain R] [IsDomain (Jou.J y)] in
lemma theta2_local (a : Localization.AtPrime PP) (ha : a ∈ maximalIdeal (Localization.AtPrime PP)) :
    theta2 y Q hyl (MvPolynomial.C a) ∈ maximalIdeal (Localization.AtPrime Q) := by
  obtain ⟨⟨p, m⟩, rfl⟩ := IsLocalization.mk'_surjective (PP).primeCompl a
  rw [IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime PP) PP] at ha
  have hs := IsLocalization.mk'_spec (Localization.AtPrime PP) p m
  have h1 : theta2 y Q hyl (MvPolynomial.C (IsLocalization.mk' _ p m)) *
      algebraMap _ (Localization.AtPrime Q) (algebraMap R (Jou.J y) (m : R)) =
      algebraMap _ (Localization.AtPrime Q) (algebraMap R (Jou.J y) p) := by
    rw [← theta2_C_algebraMap y Q hyl, ← theta2_C_algebraMap y Q hyl, ← map_mul, ← map_mul, hs]
  have hmu : IsUnit (algebraMap (Jou.J y) (Localization.AtPrime Q) (algebraMap R (Jou.J y) (m : R))) :=
    IsLocalization.map_units (Localization.AtPrime Q) (⟨_, m.2⟩ : Q.primeCompl)
  have hp : algebraMap (Jou.J y) (Localization.AtPrime Q) (algebraMap R (Jou.J y) p) ∈
      maximalIdeal (Localization.AtPrime Q) := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q]; exact ha
  rw [← h1] at hp
  exact ((maximalIdeal _).mul_unit_mem_iff_mem hmu).1 hp

end E2b

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

section T2

variable {R : Type} [CommRing R] [IsDomain R] [Algebra ℚ R] [Algebra.Smooth ℚ R] [IsNoetherianRing R]
  {r : ℕ}
  (y : Fin (r + 1) → R) [IsDomain (Jou.J y)] [IsNoetherianRing (Jou.J y)]
  [Algebra.FormallySmooth ℚ (Jou.J y)] [Algebra.FiniteType ℚ (Jou.J y)]
  (Q : Ideal (Jou.J y)) [Q.IsMaximal] {l : Fin (r + 1)}
  (hyl : y l ∉ Q.comap (algebraMap R (Jou.J y)))
include hyl

omit [Algebra.Smooth ℚ R] in
/-- **Smooth invariance along the torsor** `R_P → U_Q`. -/
theorem invAt_torsor_of_rees {J : Ideal R} (hJ : J ≠ ⊥) (hJP : J ≤ Q.comap (algebraMap R (Jou.J y)))
    {w : ℕ → ℚ} (hw : InvAt J (Q.comap (algebraMap R (Jou.J y))) w) :
    InvAt (J.map (algebraMap R (Jou.J y))) Q w := by
  obtain ⟨n, e, he, rfl⟩ := hw
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  have : IsNoetherianRing (Localization.AtPrime (Q.comap (algebraMap R (Jou.J y)))) :=
    IsLocalization.isNoetherianRing (Q.comap (algebraMap R (Jou.J y))).primeCompl _ inferInstance
  have := residueField_isIntegral Q
  obtain ⟨M, -, -⟩ := he.1
  have : Algebra.FormallySmooth ℚ (ResidueField (Localization.AtPrime Q)) :=
    (Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.1 (fe_residueField Q)).2
  have h := IsInv.transfer_mvLoc (S := Localization.AtPrime (Q.comap (algebraMap R (Jou.J y))))
    (S' := Localization.AtPrime Q) (theta2 y Q hyl) (theta2_injective y Q hyl) (theta2_surj y Q hyl)
    (theta2_local y Q hyl) M.centred (Iloc_ne_bot hJ _) (Iloc_le hJP) he
  refine ⟨n + r, pad (n + r) e, ?_, ext0_pad (Nat.le_add_right n r) e⟩
  have hmap : (Iloc J (Q.comap (algebraMap R (Jou.J y)))).map ((theta2 y Q hyl).comp MvPolynomial.C) =
      Iloc (J.map (algebraMap R (Jou.J y))) Q := by
    rw [Iloc, Iloc, Ideal.map_map, Ideal.map_map, RingHom.comp_assoc, theta2_comp]
  rw [← hmap]; exact h

end T2

section T1

variable {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B] [Algebra.Smooth ℚ B] [IsNoetherianRing B]
  (Φ : WFil B)
  (hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤)
  [IsNoetherianRing (ReesAlg Φ)] [Algebra.FormallySmooth ℚ (ReesAlg Φ)]
  [Algebra.FiniteType ℚ (ReesAlg Φ)]
  (P : Ideal (ReesAlg Φ)) [P.IsMaximal] (hsP : reesS Φ hneg ∉ P)
include hneg hsP

omit [Algebra.Smooth ℚ B] in
/-- **Smooth invariance off the exceptional divisor** `B_𝔪 → R_P`. -/
theorem invAt_rees_of_base {J : Ideal B} (hJ : J ≠ ⊥)
    (hJP : J ≤ P.comap (algebraMap B (ReesAlg Φ)))
    {u : ℕ → ℚ} (hu : InvAt J (P.comap (algebraMap B (ReesAlg Φ))) u) :
    InvAt (J.map (algebraMap B (ReesAlg Φ))) P u := by
  obtain ⟨n, e, he, rfl⟩ := hu
  have : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have : IsNoetherianRing (Localization.AtPrime (P.comap (algebraMap B (ReesAlg Φ)))) :=
    IsLocalization.isNoetherianRing (P.comap (algebraMap B (ReesAlg Φ))).primeCompl _ inferInstance
  have := residueField_isIntegral P
  obtain ⟨M, -, -⟩ := he.1
  have : Algebra.FormallySmooth ℚ (ResidueField (Localization.AtPrime P)) :=
    (Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.1 (fe_residueField P)).2
  set 𝔮 := P.comap (algebraMap B (ReesAlg Φ))
  have h := IsInv.transfer_polyLoc (S := Localization.AtPrime 𝔮) (S' := Localization.AtPrime P)
    (theta1 Φ hneg P hsP 𝔮 rfl) (theta1_injective Φ hneg P hsP 𝔮 rfl)
    (theta1_surj Φ hneg P hsP 𝔮 rfl) (theta1_local Φ hneg P hsP 𝔮 rfl) M.centred
    (Iloc_ne_bot hJ _) (Iloc_le hJP) he
  refine ⟨n + 1, pad (n + 1) e, ?_, ext0_pad (Nat.le_succ n) e⟩
  have hcomp : (theta1 Φ hneg P hsP 𝔮 rfl).comp Polynomial.C = Localization.localRingHom 𝔮 P
      (algebraMap B (ReesAlg Φ)) rfl := RingHom.ext fun a => theta1_C Φ hneg P hsP 𝔮 rfl a
  have hmap : (Iloc J 𝔮).map ((theta1 Φ hneg P hsP 𝔮 rfl).comp Polynomial.C) =
      Iloc (J.map (algebraMap B (ReesAlg Φ))) P := by
    have hc2 : (Localization.localRingHom 𝔮 P (algebraMap B (ReesAlg Φ)) rfl).comp
        (algebraMap B (Localization.AtPrime 𝔮)) =
        (algebraMap (ReesAlg Φ) (Localization.AtPrime P)).comp (algebraMap B (ReesAlg Φ)) :=
      RingHom.ext fun x => Localization.localRingHom_to_map _ _ _ rfl x
    rw [Iloc, Iloc, Ideal.map_map, Ideal.map_map, hcomp, hc2]
  rw [← hmap]; exact h

end T1

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

section Helpers

variable {A : Type} [CommRing A] [Algebra ℚ A]

lemma InvAt.congr_pt {I : Ideal A} {𝔪 𝔪' : Ideal A} [𝔪.IsPrime] [𝔪'.IsPrime] (h : 𝔪 = 𝔪')
    {v : ℕ → ℚ} (hv : InvAt I 𝔪 v) : InvAt I 𝔪' v := by
  subst h; exact hv

lemma InvAt.of_Iloc_eq {I I' : Ideal A} {𝔪 : Ideal A} [𝔪.IsPrime] (h : Iloc I 𝔪 = Iloc I' 𝔪)
    {v : ℕ → ℚ} (hv : InvAt I 𝔪 v) : InvAt I' 𝔪 v := by
  obtain ⟨n, e, he, rfl⟩ := hv
  exact ⟨n, e, h ▸ he, rfl⟩

omit [Algebra ℚ A] in
lemma Iloc_span_unit_mul {s : A} {J : Ideal A} {𝔪 : Ideal A} [𝔪.IsPrime] (hs : s ∉ 𝔪) (d : ℕ) :
    Iloc (Ideal.span {s ^ d} * J) 𝔪 = Iloc J 𝔪 := by
  rw [Iloc, Iloc, Ideal.map_mul, Ideal.map_span, Set.image_singleton]
  have hu : IsUnit (algebraMap A (Localization.AtPrime 𝔪) (s ^ d)) :=
    IsLocalization.map_units (Localization.AtPrime 𝔪)
      (⟨s ^ d, fun h => hs (‹𝔪.IsPrime›.mem_of_pow_mem d h)⟩ : 𝔪.primeCompl)
  rw [Ideal.span_singleton_eq_top.2 hu, Ideal.top_mul]

end Helpers

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)
  (hπ0 : π ≠ 0)

/-- The new ideal `I_w U` on the torsor. -/
abbrev torsorI : Ideal (Torsor hI hmax h𝔭 d hπ) :=
  (weakT (compFil hI hmax h𝔭 d) I d (I_le_compFil hI hmax h𝔭 hd)).map
    (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ))

/-- The exceptional element `s` on the torsor. -/
abbrev torsorS : Torsor hI hmax h𝔭 d hπ :=
  algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ)
    (reesS (compFil hI hmax h𝔭 d) (fun _j hj => compFil_F_nonpos hI hmax h𝔭 d hj))

lemma torsor_map_eq : I.map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) =
    Ideal.span {torsorS hI hmax h𝔭 hπ ^ d} * torsorI hI hmax h𝔭 hd hπ := by
  rw [IsScalarTower.algebraMap_eq A (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ),
    ← Ideal.map_map, map_eq_weakT _ (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj) I d
      (I_le_compFil hI hmax h𝔭 hd), Ideal.map_mul, Ideal.map_span, Set.image_singleton, map_pow]

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)
  (hπ0 : π ≠ 0)

/-- Some torsor generator is a unit at every point. -/
lemma exists_torsorY_not_mem (Q : Ideal (Torsor hI hmax h𝔭 d hπ)) [Q.IsPrime] :
    ∃ l, torsorY hI hmax h𝔭 d hπ l ∉
      Q.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ)) := by
  by_contra h
  push Not at h
  apply ‹Q.IsPrime›.ne_top
  rw [Ideal.eq_top_iff_one, ← Jou.sum_σ_mul (torsorY hI hmax h𝔭 d hπ)]
  exact Ideal.sum_mem _ fun l _ => Q.mul_mem_left _ (h l)

include hd hw in
/-- On the exceptional divisor-free part, the points lie away from `V(𝔭)`. -/
lemma torsor_not_le_of_s_not_mem (Q : Ideal (Torsor hI hmax h𝔭 d hπ)) [Q.IsPrime]
    (hsQ : torsorS hI hmax h𝔭 hπ ∉ Q) :
    ¬ 𝔭 ≤ Q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) := by
  intro hle
  obtain ⟨l, hl⟩ := exists_torsorY_not_mem hI hmax h𝔭 hπ Q
  apply hl
  set P := Q.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ))
  have hsP : reesS (compFil hI hmax h𝔭 d) (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj) ∉ P := hsQ
  have hj := genDeg_pos hI hmax h𝔭 d l
  obtain ⟨m, hm⟩ : ∃ m : ℕ, genDeg hI hmax h𝔭 d l = m := ⟨(genDeg hI hmax h𝔭 d l).toNat, by omega⟩
  have hg : genCoeff hI hmax h𝔭 d π l ∈ 𝔭 := by
    have h1 := genCoeff_mem hI hmax h𝔭 d hπ l
    rw [compFil_F] at h1
    have h2 : compF I 𝔭 ((genDeg hI hmax h𝔭 d l : ℚ) / d) ≤ compF I 𝔭 (1 / d) := by
      refine compF_antitone ?_ hI (fun 𝔪 _ h𝔭𝔪' => ?_)
      · have : (1 : ℚ) ≤ genDeg hI hmax h𝔭 d l := by exact_mod_cast hj
        have hd' : (0 : ℚ) < d := by exact_mod_cast hd
        exact div_le_div_of_nonneg_right this hd'.le
      · have hZ := mem_maxLocus_of_minimal hI hmax h𝔭 𝔪 h𝔭𝔪'
        exact ⟨hZ.1, v₀, hZ.2⟩
    rw [compF_one_div hI hmax h𝔭 hd hw] at h2
    exact h2 h1
  have hgP : algebraMap A (ReesAlg (compFil hI hmax h𝔭 d)) (genCoeff hI hmax h𝔭 d π l) ∈ P := by
    have := hle hg
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply A (ReesAlg (compFil hI hmax h𝔭 d))] at this
    exact this
  have heq : torsorY hI hmax h𝔭 d hπ l *
      reesS (compFil hI hmax h𝔭 d) (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj) ^ m =
      algebraMap A (ReesAlg (compFil hI hmax h𝔭 d)) (genCoeff hI hmax h𝔭 d π l) := by
    apply Subtype.ext
    show (LaurentPolynomial.C (genCoeff hI hmax h𝔭 d π l) * T (genDeg hI hmax h𝔭 d l)) *
      ((reesS (compFil hI hmax h𝔭 d) (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj) ^ m :
        ReesAlg (compFil hI hmax h𝔭 d)) : A[T;T⁻¹]) = algebraMap A A[T;T⁻¹] _
    rw [reesS_pow_coe, hm, mul_assoc, ← T_add, add_neg_cancel, T_zero, mul_one,
      LaurentPolynomial.C_eq_algebraMap]
  rw [← heq] at hgP
  have : P.IsPrime := Ideal.comap_isPrime _ _
  rcases ‹P.IsPrime›.mem_or_mem hgP with h | h
  · exact h
  · exact absurd (‹P.IsPrime›.mem_of_pow_mem m h) hsP

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)
  (hπ0 : π ≠ 0)

include hd hw hπ0 in
/-- **The invariant on the torsor.** At a point `Q` of `V(I_w U)`, either `s ∈ Q` and the
invariant has strictly increased, or `s ∉ Q`, `Q` lies over a point of `V(I) ∖ V(𝔭)` and the
invariant is unchanged. -/
theorem torsor_invAt (Q : Ideal (Torsor hI hmax h𝔭 d hπ)) [hQ : Q.IsMaximal]
    (hIQ : torsorI hI hmax h𝔭 hd hπ ≤ Q) {v : ℕ → ℚ}
    (hv : InvAt (torsorI hI hmax h𝔭 hd hπ) Q v) :
    (torsorS hI hmax h𝔭 hπ ∈ Q ∧ toLex v₀ < toLex v) ∨
    (torsorS hI hmax h𝔭 hπ ∉ Q ∧ I ≤ Q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) ∧
      ¬ 𝔭 ≤ Q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) ∧
      InvAt I (Q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))) v) := by
  classical
  have hneg : ∀ j : ℤ, j ≤ 0 → (compFil hI hmax h𝔭 d).F j = ⊤ :=
    fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj
  have hId := I_le_compFil hI hmax h𝔭 hd
  have : Algebra.FiniteType A (ReesAlg (compFil hI hmax h𝔭 d)) :=
    reesAlg_finiteType hI hmax h𝔭 d hd hw
  have : Algebra.FiniteType ℚ (ReesAlg (compFil hI hmax h𝔭 d)) :=
    Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have : IsNoetherianRing (ReesAlg (compFil hI hmax h𝔭 d)) :=
    Algebra.FiniteType.isNoetherianRing A (ReesAlg (compFil hI hmax h𝔭 d))
  have : Algebra.Smooth ℚ (ReesAlg (compFil hI hmax h𝔭 d)) := rees_smooth hI hmax h𝔭 hd hw
  have : IsDomain (Torsor hI hmax h𝔭 d hπ) := torsor_isDomain hI hmax h𝔭 hπ hπ0
  have : Algebra.FiniteType ℚ (Torsor hI hmax h𝔭 d hπ) := torsor_finiteType hI hmax h𝔭 hd hw hπ
  have : IsNoetherianRing (Torsor hI hmax h𝔭 d hπ) :=
    Algebra.FiniteType.isNoetherianRing ℚ (Torsor hI hmax h𝔭 d hπ)
  have : Algebra.Smooth ℚ (Torsor hI hmax h𝔭 d hπ) := torsor_smooth hI hmax h𝔭 hd hw hπ
  -- the point of the Rees algebra below `Q`
  have hPm : (Q.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d))
    (Torsor hI hmax h𝔭 d hπ))).IsMaximal := comap_isMaximal_of_finiteType Q
  have hIwP : weakT (compFil hI hmax h𝔭 d) I d hId ≤
      Q.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ)) :=
    Ideal.map_le_iff_le_comap.1 hIQ
  obtain ⟨l, hl⟩ := exists_torsorY_not_mem hI hmax h𝔭 hπ Q
  have hIw0 : weakT (compFil hI hmax h𝔭 d) I d hId ≠ ⊥ :=
    weakT_ne_bot (compFil hI hmax h𝔭 d) hI d hId
  obtain ⟨w, hw'⟩ := exists_invAt hIw0 _ hIwP
  have hwU : InvAt (torsorI hI hmax h𝔭 hd hπ) Q w :=
    invAt_torsor_of_rees (torsorY hI hmax h𝔭 d hπ) Q hl hIw0 hIwP hw'
  obtain rfl : v = w := hv.unique hwU
  by_cases hsQ : torsorS hI hmax h𝔭 hπ ∈ Q
  · left
    refine ⟨hsQ, ?_⟩
    exact drop hI hmax h𝔭 hd hw _ hIwP hsQ (genDeg_pos hI hmax h𝔭 d l)
      (genCoeff_mem hI hmax h𝔭 d hπ l) hl hw'
  · right
    have hcomap : Q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) =
        (Q.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ))).comap
          (algebraMap A (ReesAlg (compFil hI hmax h𝔭 d))) := by
      rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    have hI𝔪 : I ≤ Q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) := by
      rw [← Ideal.map_le_iff_le_comap, torsor_map_eq hI hmax h𝔭 hd hπ]
      exact Ideal.mul_le_right.trans hIQ
    refine ⟨hsQ, hI𝔪, torsor_not_le_of_s_not_mem hI hmax h𝔭 hd hw hπ Q hsQ, ?_⟩
    have h𝔪m : (Q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).IsMaximal :=
      comap_isMaximal_of_finiteType Q
    obtain ⟨u, hu⟩ := exists_invAt hI _ hI𝔪
    have hu' := InvAt.congr_pt hcomap hu
    have hI𝔪' : I ≤ (Q.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d))
        (Torsor hI hmax h𝔭 d hπ))).comap (algebraMap A (ReesAlg (compFil hI hmax h𝔭 d))) :=
      hcomap ▸ hI𝔪
    have hR := invAt_rees_of_base (compFil hI hmax h𝔭 d) hneg _ hsQ hI hI𝔪' hu'
    rw [map_eq_weakT _ hneg I d hId] at hR
    have hR' := InvAt.of_Iloc_eq (Iloc_span_unit_mul (s := reesS (compFil hI hmax h𝔭 d) hneg)
      (𝔪 := Q.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ))) hsQ d) hR
    obtain rfl : u = v := hR'.unique hw'
    exact hu

end BezoutCounterexample.Principalization




namespace BezoutCounterexample.Principalization

open LaurentPolynomial

section ReesQuot

variable {B : Type*} [CommRing B] [Algebra ℚ B] (Φ : WFil B) (𝔞 : Ideal B)

/-- Reduction of the Rees algebra modulo `𝔞` into `(B/𝔞)[T^±]`. -/
def reesRed : ReesAlg Φ →+* (B ⧸ 𝔞)[T;T⁻¹] :=
  (lmap (Ideal.Quotient.mk 𝔞)).comp (ReesAlg Φ).val.toRingHom

omit [Algebra ℚ B] in
lemma reesRed_coeff (p : ReesAlg Φ) (j : ℤ) :
    (reesRed Φ 𝔞 p).coeff j = Ideal.Quotient.mk 𝔞 ((p : B[T;T⁻¹]).coeff j) :=
  lmap_coeff _ _ _

omit [Algebra ℚ B] in
lemma exists_mem_map_rees {j : ℤ} {x : B} (hx : x ∈ Φ.F j * 𝔞) :
    ∃ q ∈ 𝔞.map (algebraMap B (ReesAlg Φ)), (q : B[T;T⁻¹]) = LaurentPolynomial.C x * T j := by
  refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun x y hx hy => ?_)
  · refine ⟨⟨LaurentPolynomial.C a * T j, C_mul_T_mem_ReesAlg ha⟩ * algebraMap B (ReesAlg Φ) b,
      Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hb), ?_⟩
    show LaurentPolynomial.C a * T j * algebraMap B B[T;T⁻¹] b = _
    rw [← LaurentPolynomial.C_eq_algebraMap, map_mul]; ring
  · obtain ⟨q, hq, h⟩ := hx
    obtain ⟨q', hq', h'⟩ := hy
    exact ⟨q + q', add_mem hq hq', by
      show (q : B[T;T⁻¹]) + q' = _
      rw [h, h', map_add, add_mul]⟩

omit [Algebra ℚ B] in
/-- **`𝔞 R` is the kernel of the reduction** when `𝔞` is comaximal to every `F_j`. -/
theorem map_eq_ker_reesRed (h : ∀ j, Φ.F j ⊔ 𝔞 = ⊤) :
    𝔞.map (algebraMap B (ReesAlg Φ)) = RingHom.ker (reesRed Φ 𝔞) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, RingHom.mem_ker]
    ext j
    rw [reesRed_coeff]
    show Ideal.Quotient.mk 𝔞 ((algebraMap B B[T;T⁻¹] b).coeff j) = _
    rw [← LaurentPolynomial.C_eq_algebraMap, LaurentPolynomial.C_apply]
    split_ifs
    · simp [Ideal.Quotient.eq_zero_iff_mem.2 hb]
    · simp
  · intro p hp
    rw [RingHom.mem_ker] at hp
    rw [← sum_hcomp Φ p]
    refine Ideal.sum_mem _ fun j _ => ?_
    have h1 : (p : B[T;T⁻¹]).coeff j ∈ 𝔞 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← reesRed_coeff, hp]; rfl
    have h2 : (p : B[T;T⁻¹]).coeff j ∈ Φ.F j * 𝔞 := by
      rw [Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.2 (h j))]
      exact ⟨p.2 j, h1⟩
    obtain ⟨q, hq, hq'⟩ := exists_mem_map_rees Φ 𝔞 h2
    have : q = hcomp Φ p j := Subtype.ext hq'
    rw [← this]; exact hq

omit [Algebra ℚ B] in
theorem isPrime_map_rees [IsDomain (B ⧸ 𝔞)] (h : ∀ j, Φ.F j ⊔ 𝔞 = ⊤) :
    (𝔞.map (algebraMap B (ReesAlg Φ))).IsPrime := by
  rw [map_eq_ker_reesRed Φ 𝔞 h]
  exact RingHom.ker_isPrime _

end ReesQuot

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)
  (hπ0 : π ≠ 0)

include hd hw in
lemma compFil_sup_eq_top {𝔭' : Ideal A} (h𝔭' : 𝔭' ∈ (locusIdeal I v₀).minimalPrimes)
    (hne : 𝔭 ≠ 𝔭') (j : ℤ) : (compFil hI hmax h𝔭 d).F j ⊔ 𝔭' = ⊤ := by
  have hsup := minimalPrimes_sup_eq_top hI hmax h𝔭 h𝔭' hne
  by_cases hj : j ≤ 0
  · rw [compFil_F_nonpos hI hmax h𝔭 d hj, top_sup_eq]
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, j = N := ⟨j.toNat, by omega⟩
    have h1 : 𝔭 ^ N ≤ (compFil hI hmax h𝔭 d).F N := by
      rw [compFil_F]; push_cast; exact pow_le_compF hI hmax h𝔭 hd hw N
    have h2 : 𝔭 ^ N ⊔ 𝔭' = ⊤ := by
      rw [← Ideal.isCoprime_iff_sup_eq] at hsup ⊢; exact hsup.pow_left
    exact eq_top_iff.2 (h2 ▸ sup_le_sup_right h1 _)

include hd hw in
lemma exists_torsorY_not_mem_map {𝔭' : Ideal A} (h𝔭' : 𝔭' ∈ (locusIdeal I v₀).minimalPrimes)
    (hne : 𝔭 ≠ 𝔭') : ∃ l, torsorY hI hmax h𝔭 d hπ l ∉
      𝔭'.map (algebraMap A (ReesAlg (compFil hI hmax h𝔭 d))) := by
  have hF1 : ¬ (compFil hI hmax h𝔭 d).F 1 ≤ 𝔭' := by
    intro hle
    rw [compFil_F, show ((1 : ℤ) : ℚ) / d = 1 / d by push_cast; ring,
      compF_one_div hI hmax h𝔭 hd hw] at hle
    have := minimalPrimes_sup_eq_top hI hmax h𝔭 h𝔭' hne
    rw [sup_eq_right.2 hle] at this
    exact h𝔭'.1.1.ne_top this
  obtain ⟨g, hg, hg'⟩ : ∃ g ∈ gensF hI hmax h𝔭 d 1, g ∉ 𝔭' := by
    by_contra hcon
    push Not at hcon
    apply hF1
    rw [← span_gensF]
    exact Ideal.span_le.2 hcon
  obtain ⟨l, hl1, hl2⟩ := exists_index hI hmax h𝔭 (π := π) le_rfl (by exact_mod_cast hd) hg
  refine ⟨l, fun hmem => hg' ?_⟩
  rw [map_eq_ker_reesRed _ _ (compFil_sup_eq_top hI hmax h𝔭 hd hw h𝔭' hne), RingHom.mem_ker] at hmem
  have h1 := congrArg (fun p => p.coeff 1) hmem
  simp only [reesRed_coeff] at h1
  have h2 : ((torsorY hI hmax h𝔭 d hπ l : ReesAlg (compFil hI hmax h𝔭 d)) : A[T;T⁻¹]).coeff 1 = g := by
    simp [torsorY, hl1, hl2, coeff_C_mul_T]
  have h3 : Ideal.Quotient.mk 𝔭' g = 0 := by
    rw [← h2]; simpa using h1
  exact Ideal.Quotient.eq_zero_iff_mem.1 h3

include hd hw in
/-- **The other components stay prime on the torsor.** -/
theorem torsor_comp_isPrime {𝔭' : Ideal A} (h𝔭' : 𝔭' ∈ (locusIdeal I v₀).minimalPrimes)
    (hne : 𝔭 ≠ 𝔭') : (𝔭'.map (algebraMap A (Torsor hI hmax h𝔭 d hπ))).IsPrime := by
  have := h𝔭'.1.1
  have : (𝔭'.map (algebraMap A (ReesAlg (compFil hI hmax h𝔭 d)))).IsPrime :=
    isPrime_map_rees _ _ (compFil_sup_eq_top hI hmax h𝔭 hd hw h𝔭' hne)
  obtain ⟨l, hl⟩ := exists_torsorY_not_mem_map hI hmax h𝔭 hd hw hπ h𝔭' hne
  rw [IsScalarTower.algebraMap_eq A (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ),
    ← Ideal.map_map]
  exact Jou.isPrime_map _ hl

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

section Count

variable {U : Type*} [CommRing U] [IsJacobsonRing U]

/-- The minimal primes of the ideal of a set `S` of points covered by finitely many prime
"components" `𝔯 i` (each entirely contained in `S`) are among the `𝔯 i`. -/
theorem minimalPrimes_sInf_subset {S : Set (Ideal U)} {ι : Type*} (s : Finset ι)
    (𝔯 : ι → Ideal U) (hprime : ∀ i ∈ s, (𝔯 i).IsPrime)
    (hcov : ∀ Q ∈ S, ∃ i ∈ s, 𝔯 i ≤ Q)
    (hback : ∀ i ∈ s, ∀ Q : Ideal U, Q.IsMaximal → 𝔯 i ≤ Q → Q ∈ S) :
    (sInf S).minimalPrimes ⊆ 𝔯 '' (s : Set ι) := by
  classical
  intro 𝔮 h𝔮
  have h𝔮p : 𝔮.IsPrime := h𝔮.1.1
  have hprod : s.prod 𝔯 ≤ sInf S := by
    refine le_sInf fun Q hQ => ?_
    obtain ⟨i, hi, hle⟩ := hcov Q hQ
    exact Ideal.prod_le_inf.trans ((Finset.inf_le hi).trans hle)
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst hs
    rw [Finset.prod_empty, Ideal.one_eq_top] at hprod
    exact absurd (eq_top_iff.2 (hprod.trans h𝔮.1.2)) h𝔮p.ne_top
  obtain ⟨i, hi, hle⟩ := h𝔮p.prod_le.1 (hprod.trans h𝔮.1.2)
  have := hprime i hi
  have hjac : sInf S ≤ 𝔯 i := by
    rw [← IsJacobsonRing.out ‹IsJacobsonRing U› (Ideal.IsPrime.isRadical (hprime i hi)),
      Ideal.jacobson]
    exact sInf_le_sInf fun Q hQ => hback i hi Q hQ.2 hQ.1
  exact ⟨i, hi, le_antisymm hle (h𝔮.2 ⟨hprime i hi, hjac⟩ hle)⟩

theorem ncard_minimalPrimes_sInf_le {S : Set (Ideal U)} {ι : Type*} (s : Finset ι)
    (𝔯 : ι → Ideal U) (hprime : ∀ i ∈ s, (𝔯 i).IsPrime)
    (hcov : ∀ Q ∈ S, ∃ i ∈ s, 𝔯 i ≤ Q)
    (hback : ∀ i ∈ s, ∀ Q : Ideal U, Q.IsMaximal → 𝔯 i ≤ Q → Q ∈ S) :
    (sInf S).minimalPrimes.ncard ≤ s.card := by
  have h := minimalPrimes_sInf_subset s 𝔯 hprime hcov hback
  calc (sInf S).minimalPrimes.ncard ≤ (𝔯 '' (s : Set ι)).ncard :=
        Set.ncard_le_ncard h ((s.finite_toSet).image _)
    _ ≤ (s : Set ι).ncard := Set.ncard_image_le s.finite_toSet
    _ = s.card := Set.ncard_coe_finset s

end Count

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)
  (hπ0 : π ≠ 0)

include hd hw in
/-- A point containing `s` lies over `V(𝔭)`. -/
lemma le_comap_of_s_mem (Q : Ideal (Torsor hI hmax h𝔭 d hπ)) (hsQ : torsorS hI hmax h𝔭 hπ ∈ Q) :
    𝔭 ≤ Q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) := by
  intro g hg
  have hg1 : g ∈ (compFil hI hmax h𝔭 d).F 1 := by
    rw [compFil_F, show ((1 : ℤ) : ℚ) / d = 1 / d by push_cast; ring,
      compF_one_div hI hmax h𝔭 hd hw]
    exact hg
  rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply A (ReesAlg (compFil hI hmax h𝔭 d))
    (Torsor hI hmax h𝔭 d hπ)]
  have : algebraMap A (ReesAlg (compFil hI hmax h𝔭 d)) g =
      reesS (compFil hI hmax h𝔭 d) (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj) *
        ⟨LaurentPolynomial.C g * T 1, C_mul_T_mem_ReesAlg hg1⟩ := by
    apply Subtype.ext
    show algebraMap A A[T;T⁻¹] g = T (-1) * (LaurentPolynomial.C g * T 1)
    rw [mul_left_comm, ← T_add, neg_add_cancel, T_zero, mul_one, LaurentPolynomial.C_eq_algebraMap]
  rw [this, map_mul]
  exact Q.mul_mem_right _ hsQ

include hπ0 in
theorem torsorI_ne_bot : torsorI hI hmax h𝔭 hd hπ ≠ ⊥ := by
  have hinj : Function.Injective (algebraMap (ReesAlg (compFil hI hmax h𝔭 d))
      (Torsor hI hmax h𝔭 d hπ)) := Jou.algebraMap_injective (torsorY_zero_ne hI hmax h𝔭 hπ hπ0)
  rw [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
  exact weakT_ne_bot _ hI d _

include hd hw hπ0 in
/-- Invariants on the torsor are at least `v₀`. -/
theorem torsor_inv_ge (Q : Ideal (Torsor hI hmax h𝔭 d hπ)) [Q.IsMaximal]
    (hIQ : torsorI hI hmax h𝔭 hd hπ ≤ Q) {v : ℕ → ℚ}
    (hv : InvAt (torsorI hI hmax h𝔭 hd hπ) Q v) : toLex v₀ ≤ toLex v := by
  have : Algebra.FiniteType ℚ (Torsor hI hmax h𝔭 d hπ) := torsor_finiteType hI hmax h𝔭 hd hw hπ
  rcases torsor_invAt hI hmax h𝔭 hd hw hπ hπ0 Q hIQ hv with ⟨-, hlt⟩ | ⟨-, hI𝔪, -, hv'⟩
  · exact hlt.le
  · have : (Q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).IsMaximal :=
      comap_isMaximal_of_finiteType Q
    exact hmax _ hI𝔪 v hv'

include hd hw hπ0 in
/-- Points over the other components belong to the new maximal locus. -/
theorem mem_maxLocus_torsor {𝔭' : Ideal A} (h𝔭' : 𝔭' ∈ (locusIdeal I v₀).minimalPrimes)
    (hne : 𝔭 ≠ 𝔭') (Q : Ideal (Torsor hI hmax h𝔭 d hπ)) [hQ : Q.IsMaximal]
    (hle : 𝔭'.map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) ≤ Q) :
    Q ∈ maxLocus (torsorI hI hmax h𝔭 hd hπ) v₀ := by
  have : IsDomain (Torsor hI hmax h𝔭 d hπ) := torsor_isDomain hI hmax h𝔭 hπ hπ0
  have : Algebra.FiniteType ℚ (Torsor hI hmax h𝔭 d hπ) := torsor_finiteType hI hmax h𝔭 hd hw hπ
  have : IsNoetherianRing (Torsor hI hmax h𝔭 d hπ) :=
    Algebra.FiniteType.isNoetherianRing ℚ (Torsor hI hmax h𝔭 d hπ)
  have : Algebra.Smooth ℚ (Torsor hI hmax h𝔭 d hπ) := torsor_smooth hI hmax h𝔭 hd hw hπ
  have h𝔪 : 𝔭' ≤ Q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) := Ideal.map_le_iff_le_comap.1 hle
  have : (Q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).IsMaximal :=
    comap_isMaximal_of_finiteType Q
  obtain ⟨hI𝔪, hinv⟩ := mem_maxLocus_of_minimal hI hmax h𝔭' _ h𝔪
  have hn𝔭 : ¬ 𝔭 ≤ Q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) := fun h => by
    have := minimalPrimes_sup_eq_top hI hmax h𝔭 h𝔭' hne
    exact (Ideal.IsMaximal.ne_top ‹_›) (eq_top_iff.2 (this ▸ sup_le h h𝔪))
  have hsQ : torsorS hI hmax h𝔭 hπ ∉ Q := fun h => hn𝔭 (le_comap_of_s_mem hI hmax h𝔭 hd hw hπ Q h)
  have hIQ : torsorI hI hmax h𝔭 hd hπ ≤ Q := by
    have h1 : I.map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) ≤ Q := Ideal.map_le_iff_le_comap.2 hI𝔪
    rw [torsor_map_eq hI hmax h𝔭 hd hπ] at h1
    rcases hQ.isPrime.mul_le.1 h1 with h | h
    · exact absurd (hQ.isPrime.mem_of_pow_mem d (h (Ideal.mem_span_singleton_self _))) hsQ
    · exact h
  obtain ⟨v, hv⟩ := exists_invAt (torsorI_ne_bot hI hmax h𝔭 hd hπ hπ0) Q hIQ
  rcases torsor_invAt hI hmax h𝔭 hd hw hπ hπ0 Q hIQ hv with ⟨h, -⟩ | ⟨-, -, -, hv'⟩
  · exact absurd h hsQ
  · obtain rfl : v₀ = v := hinv.unique hv'
    exact ⟨hQ, hIQ, hv⟩

include hd hw hπ0 in
/-- **The number of components drops.** -/
theorem torsor_count :
    (locusIdeal (torsorI hI hmax h𝔭 hd hπ) v₀).minimalPrimes.ncard <
      (locusIdeal I v₀).minimalPrimes.ncard := by
  classical
  have : Algebra.FiniteType ℚ (Torsor hI hmax h𝔭 d hπ) := torsor_finiteType hI hmax h𝔭 hd hw hπ
  have : IsJacobsonRing (Torsor hI hmax h𝔭 d hπ) := isJacobsonRing_of_finiteType (A := ℚ)
  have hfin : (locusIdeal I v₀).minimalPrimes.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing A _
  have hle := ncard_minimalPrimes_sInf_le (S := maxLocus (torsorI hI hmax h𝔭 hd hπ) v₀)
    (hfin.toFinset.erase 𝔭) (fun 𝔭' => 𝔭'.map (algebraMap A (Torsor hI hmax h𝔭 d hπ))) ?_ ?_ ?_
  · have hcard : (hfin.toFinset.erase 𝔭).card < (locusIdeal I v₀).minimalPrimes.ncard := by
      rw [Set.ncard_eq_toFinset_card _ hfin]
      exact Finset.card_erase_lt_of_mem (hfin.mem_toFinset.2 h𝔭)
    exact lt_of_le_of_lt hle hcard
  · intro 𝔭' h𝔭'
    rw [Finset.mem_erase, Set.Finite.mem_toFinset] at h𝔭'
    exact torsor_comp_isPrime hI hmax h𝔭 hd hw hπ h𝔭'.2 (Ne.symm h𝔭'.1)
  · intro Q hQ
    obtain ⟨hQm, hIQ, hv⟩ := hQ
    rcases torsor_invAt hI hmax h𝔭 hd hw hπ hπ0 Q hIQ hv with ⟨-, hlt⟩ | ⟨-, hI𝔪, hn𝔭, hv'⟩
    · exact absurd hlt (lt_irrefl _)
    · have : (Q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).IsMaximal :=
        comap_isMaximal_of_finiteType Q
      have hL : locusIdeal I v₀ ≤ Q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) :=
        sInf_le ⟨inferInstance, hI𝔪, hv'⟩
      obtain ⟨𝔭', h𝔭', h𝔭'le⟩ := Ideal.exists_minimalPrimes_le hL
      refine ⟨𝔭', ?_, Ideal.map_le_iff_le_comap.2 h𝔭'le⟩
      rw [Finset.mem_erase, Set.Finite.mem_toFinset]
      exact ⟨fun h => hn𝔭 (h ▸ h𝔭'le), h𝔭'⟩
  · intro 𝔭' h𝔭' Q hQ hle
    rw [Finset.mem_erase, Set.Finite.mem_toFinset] at h𝔭'
    exact mem_maxLocus_torsor hI hmax h𝔭 hd hw hπ hπ0 h𝔭'.2 (Ne.symm h𝔭'.1) Q hle

end BezoutCounterexample.Principalization

