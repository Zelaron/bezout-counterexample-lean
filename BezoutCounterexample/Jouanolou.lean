import BezoutCounterexample.Principalization.ReesSmooth
import BezoutCounterexample.Nagata

/-!
# Jouanolou rings

Lemma 3.1 (`lem:jouanolou`) of the paper.

The ring `J(c) = B[σ₀, …, σ_{r-1}]/(∑ σᵢ cᵢ - 1)` for `c : Fin r → B`:

* `Jou.isDomain`: a domain over a domain (if some `cₗ ≠ 0`), via the elimination map
  `Jou.elim` to `B[1/cₗ][σ_{≠l}]` (`Jou.isLocalization_elim`);
* `Jou.ufd`: a UFD over a Noetherian UFD when some `cₗ` is prime and does not divide another
  `cₘ` (Nagata's criterion);
* `Jou.quotEquiv`, `Jou.isLocalization_map`, `Jou.equivPoly`: reduction, localization and the
  case of a unit;
* `Jou.liftDer`: lifting derivations; `Jou.formallySmooth`: formal smoothness over `B`.
-/

noncomputable section


namespace BezoutCounterexample.Jou

open MvPolynomial

variable {B : Type*} [CommRing B] {r : ℕ}

/-- The Jouanolou relation `∑ σᵢ cᵢ - 1`. -/
def rel (c : Fin r → B) : MvPolynomial (Fin r) B := ∑ i, X i * C (c i) - 1

/-- The Jouanolou ring `B[σ]/(∑ σᵢ cᵢ - 1)`. -/
abbrev J (c : Fin r → B) := MvPolynomial (Fin r) B ⧸ Ideal.span {rel c}

/-- The quotient map. -/
abbrev mk (c : Fin r → B) : MvPolynomial (Fin r) B →ₐ[B] J c := Ideal.Quotient.mkₐ B _

/-- The coordinates `σᵢ`. -/
def σ (c : Fin r → B) (i : Fin r) : J c := mk c (X i)

lemma mk_rel (c : Fin r → B) : mk c (rel c) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)

lemma mk_C (c : Fin r → B) (a : B) : mk c (C a) = algebraMap B (J c) a := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]

lemma sum_σ_mul (c : Fin r → B) : ∑ i, σ c i * algebraMap B (J c) (c i) = 1 := by
  have h1 : ∑ i, σ c i * algebraMap B (J c) (c i) = mk c (∑ i, X i * C (c i)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, mk_C]; rfl
  have h2 : (∑ i, X i * C (c i) : MvPolynomial (Fin r) B) = rel c + 1 := by
    rw [rel, sub_add_cancel]
  rw [h1, h2, map_add, mk_rel, map_one, zero_add]

lemma map_rel {D : Type*} [CommRing D] (f : B →+* D) (c : Fin r → B) :
    MvPolynomial.map f (rel c) = rel (f ∘ c) := by
  simp [rel]

/-- `∑ σᵢ cᵢ - 1` is a nonzerodivisor (its constant coefficient is a unit). -/
lemma rel_nzd {D : Type*} [CommRing D] (c : Fin r → D) {p : MvPolynomial (Fin r) D}
    (h : p * rel c = 0) : p = 0 := by
  have hu : IsUnit ((rel c : MvPolynomial (Fin r) D) : MvPowerSeries (Fin r) D) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPolynomial.coeff_coe, ← MvPolynomial.constantCoeff_eq]
    have : MvPolynomial.constantCoeff (rel c) = -1 := by
      rw [rel]; simp
    rw [this]; exact isUnit_one.neg
  have h2 : ((p : MvPolynomial (Fin r) D) : MvPowerSeries (Fin r) D) *
      ((rel c : MvPolynomial (Fin r) D) : MvPowerSeries (Fin r) D) = 0 := by
    rw [← MvPolynomial.coe_mul, h, MvPolynomial.coe_zero]
  have h3 := hu.mul_left_eq_zero.1 h2
  exact MvPolynomial.coe_injective (Fin r) D (h3.trans MvPolynomial.coe_zero.symm)

/-- Nonzero constants are nonzerodivisors modulo the Jouanolou relation. -/
lemma C_mul_mem [IsDomain B] (c : Fin r → B) {b : B} (hb : b ≠ 0) {p : MvPolynomial (Fin r) B}
    (h : C b * p ∈ Ideal.span {rel c}) : p ∈ Ideal.span {rel c} := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h
  set π := Ideal.Quotient.mk (Ideal.span {b})
  have h1 : MvPolynomial.map π a * rel (π ∘ c) = 0 := by
    have := congrArg (MvPolynomial.map π) ha
    rw [map_mul, map_mul, map_C, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self b),
      C_0, zero_mul, map_rel] at this
    exact this
  have h2 := rel_nzd _ h1
  have h3 : a ∈ Ideal.map (C : B →+* MvPolynomial (Fin r) B) (RingHom.ker π) := by
    rw [← MvPolynomial.ker_map]; exact h2
  rw [Ideal.mk_ker, Ideal.map_span, Set.image_singleton] at h3
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 h3
  have hCb : (C b : MvPolynomial (Fin r) B) ≠ 0 := by simpa using hb
  have : C b * p = C b * (a' * rel c) := by rw [← ha, ← ha']; ring
  rw [mul_left_cancel₀ hCb this]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

lemma algebraMap_mul_eq_zero [IsDomain B] (c : Fin r → B) {b : B} (hb : b ≠ 0) {u : J c}
    (h : algebraMap B (J c) b * u = 0) : u = 0 := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective u
  rw [IsScalarTower.algebraMap_apply B (MvPolynomial (Fin r) B), MvPolynomial.algebraMap_eq,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at h
  exact Ideal.Quotient.eq_zero_iff_mem.2 (C_mul_mem c hb h)

end BezoutCounterexample.Jou


namespace BezoutCounterexample.Jou

open MvPolynomial

variable {B : Type*} [CommRing B] {r : ℕ}

section Solve

variable (c : Fin (r + 1) → B) (l : Fin (r + 1))

/-- `σ_l` solved from the relation, over a ring where `c_l` is a unit. -/
def solveVals {L : Type*} [CommRing L] (φ : B →+* L) (u : Lˣ) :
    Fin (r + 1) → MvPolynomial (Fin r) L :=
  Fin.insertNth l (C (↑u⁻¹ : L) * (1 - ∑ j, X j * C (φ (c (l.succAbove j))))) (fun j => X j)

/-- Eliminating `σ_l`: `B[σ] → L[σ_{≠l}]` (when `φ (c l) = u` is a unit). -/
def elimHom {L : Type*} [CommRing L] (φ : B →+* L) (u : Lˣ) :
    MvPolynomial (Fin (r + 1)) B →+* MvPolynomial (Fin r) L :=
  eval₂Hom (C.comp φ) (solveVals c l φ u)

variable {c l}

lemma elimHom_rel {L : Type*} [CommRing L] (φ : B →+* L) (u : Lˣ) (hu : φ (c l) = u) :
    elimHom c l φ u (rel c) = 0 := by
  simp only [elimHom, rel, map_sub, map_sum, map_mul, eval₂Hom_X', eval₂Hom_C, RingHom.comp_apply,
    map_one]
  rw [Fin.sum_univ_succAbove _ l]
  simp only [solveVals, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, hu]
  have : (C (↑u⁻¹ : L) * (1 - ∑ j, X j * C (φ (c (l.succAbove j))))) * C (u : L) =
      (1 - ∑ j, X j * C (φ (c (l.succAbove j))) : MvPolynomial (Fin r) L) := by
    rw [mul_comm, ← mul_assoc, ← C_mul, Units.mul_inv, C_1, one_mul]
  rw [this]; ring

lemma elimHom_rename {L : Type*} [CommRing L] (φ : B →+* L) (u : Lˣ) (p : MvPolynomial (Fin r) B) :
    elimHom c l φ u (rename l.succAbove p) = MvPolynomial.map φ p := by
  have : (elimHom c l φ u).comp (rename l.succAbove).toRingHom = MvPolynomial.map φ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp [elimHom]
    · simp [elimHom, solveVals, Fin.insertNth_apply_succAbove]
  exact congrArg (fun f : MvPolynomial (Fin r) B →+* MvPolynomial (Fin r) L => f p) this

/-- **Pseudo-division** by the Jouanolou relation, eliminating `σ_l`. -/
lemma exists_pseudo (p : MvPolynomial (Fin (r + 1)) B) :
    ∃ (N : ℕ) (q : MvPolynomial (Fin (r + 1)) B) (p₀ : MvPolynomial (Fin r) B),
      C (c l) ^ N * p = q * rel c + rename l.succAbove p₀ := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0, 0, C a, by simp⟩
  | add p p' ih ih' =>
    obtain ⟨N, q, p₀, h⟩ := ih
    obtain ⟨N', q', p₀', h'⟩ := ih'
    refine ⟨N + N', C (c l) ^ N' * q + C (c l) ^ N * q',
      C (c l) ^ N' * p₀ + C (c l) ^ N * p₀', ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, rename_C, pow_add, mul_add]
    calc C (c l) ^ N * C (c l) ^ N' * p + C (c l) ^ N * C (c l) ^ N' * p'
        = C (c l) ^ N' * (C (c l) ^ N * p) + C (c l) ^ N * (C (c l) ^ N' * p') := by ring
      _ = _ := by rw [h, h']; ring
  | mul_X p i ih =>
    obtain ⟨N, q, p₀, h⟩ := ih
    by_cases hi : i = l
    · subst hi
      set g₀ : MvPolynomial (Fin r) B := 1 - ∑ j, X j * C (c (i.succAbove j))
      have hg : X i * C (c i) = rel c + rename i.succAbove g₀ := by
        simp only [g₀, rel, map_sub, map_one, map_sum, map_mul, rename_X, rename_C]
        rw [Fin.sum_univ_succAbove _ i]; ring
      refine ⟨N + 1, q * (rel c + rename i.succAbove g₀) + rename i.succAbove p₀,
        p₀ * g₀, ?_⟩
      calc C (c i) ^ (N + 1) * (p * X i) = (C (c i) ^ N * p) * (X i * C (c i)) := by ring
        _ = _ := by rw [h, hg, map_mul]; ring
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      refine ⟨N, q * X (l.succAbove j), p₀ * X j, ?_⟩
      calc C (c l) ^ N * (p * X (l.succAbove j)) = (C (c l) ^ N * p) * X (l.succAbove j) := by ring
        _ = _ := by rw [h, map_mul, rename_X]; ring

/-- The induced map on the Jouanolou ring. -/
def elim {L : Type*} [CommRing L] (φ : B →+* L) (u : Lˣ) (hu : φ (c l) = u) :
    J c →+* MvPolynomial (Fin r) L :=
  Ideal.Quotient.lift _ (elimHom c l φ u) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, elimHom_rel φ u hu, mul_zero])

lemma elim_mk {L : Type*} [CommRing L] (φ : B →+* L) (u : Lˣ) (hu : φ (c l) = u)
    (p : MvPolynomial (Fin (r + 1)) B) : elim φ u hu (Ideal.Quotient.mk _ p) = elimHom c l φ u p :=
  rfl

/-- **Injectivity of the elimination** over a domain. -/
theorem elim_injective [IsDomain B] (hl : c l ≠ 0) {L : Type*} [CommRing L] (φ : B →+* L)
    (hφ : Function.Injective φ) (u : Lˣ) (hu : φ (c l) = u) :
    Function.Injective (elim φ u hu) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [elim_mk] at hz
  obtain ⟨N, q, p₀, h⟩ := exists_pseudo (c := c) (l := l) p
  have h1 : elimHom c l φ u (C (c l) ^ N * p) = 0 := by rw [map_mul, hz, mul_zero]
  rw [h, map_add, map_mul, elimHom_rel φ u hu, mul_zero, zero_add, elimHom_rename] at h1
  have hp₀ : p₀ = 0 := MvPolynomial.map_injective φ hφ (by rw [h1, map_zero])
  rw [hp₀, map_zero, add_zero, ← map_pow] at h
  have hmem : C (c l ^ N) * p ∈ Ideal.span {rel c} := by
    rw [h]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  exact Ideal.Quotient.eq_zero_iff_mem.2 (C_mul_mem c (pow_ne_zero N hl) hmem)

/-- **The Jouanolou ring over a domain is a domain** (if some `cₗ ≠ 0`). -/
theorem isDomain [IsDomain B] (hl : c l ≠ 0) : IsDomain (J c) := by
  set L := Localization.Away (c l)
  have hinj : Function.Injective (algebraMap B L) := IsLocalization.injective L
    (powers_le_nonZeroDivisors_of_noZeroDivisors hl)
  haveI : IsDomain L := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors hl)
  have hu : IsUnit (algebraMap B L (c l)) := IsLocalization.Away.algebraMap_isUnit _
  exact (elim_injective hl (algebraMap B L) hinj hu.unit rfl).isDomain _

end Solve

end BezoutCounterexample.Jou


namespace BezoutCounterexample.Jou

open MvPolynomial

variable {B : Type*} [CommRing B] {r : ℕ}

section Away

variable {c : Fin (r + 1) → B} {l : Fin (r + 1)}

lemma elim_algebraMap {L : Type*} [CommRing L] (φ : B →+* L) (u : Lˣ) (hu : φ (c l) = u) (b : B) :
    elim φ u hu (algebraMap B (J c) b) = C (φ b) := by
  have : algebraMap B (J c) b = Ideal.Quotient.mk _ (C b) := by
    rw [IsScalarTower.algebraMap_apply B (MvPolynomial (Fin (r + 1)) B), MvPolynomial.algebraMap_eq,
      Ideal.Quotient.algebraMap_eq]
  rw [this, elim_mk]; simp [elimHom]

lemma elim_σ {L : Type*} [CommRing L] (φ : B →+* L) (u : Lˣ) (hu : φ (c l) = u) (j : Fin r) :
    elim φ u hu (σ c (l.succAbove j)) = X j := by
  show elim φ u hu (Ideal.Quotient.mk _ (X (l.succAbove j))) = _
  rw [elim_mk]
  simp [elimHom, solveVals, Fin.insertNth_apply_succAbove]

variable (c l) in
/-- The localized polynomial ring `B[1/c_l][σ_{≠l}]`. -/
abbrev LocP := MvPolynomial (Fin r) (Localization.Away (c l))

variable (c l) in
/-- The elimination map to `B[1/c_l][σ_{≠l}]`. -/
def elimLoc : J c →+* LocP c l :=
  elim (algebraMap B (Localization.Away (c l)))
    (IsLocalization.Away.algebraMap_isUnit (c l)).unit rfl

lemma elimLoc_algebraMap (b : B) :
    elimLoc c l (algebraMap B (J c) b) = C (algebraMap B (Localization.Away (c l)) b) :=
  elim_algebraMap _ _ _ b

lemma elimLoc_σ (j : Fin r) : elimLoc c l (σ c (l.succAbove j)) = X j := elim_σ _ _ _ j

/-- `J[1/c_l] ≅ B[1/c_l][σ_{≠l}]`. -/
theorem isLocalization_elim [IsDomain B] (hl : c l ≠ 0) :
    @IsLocalization.Away _ _ (algebraMap B (J c) (c l)) (LocP c l) _ (elimLoc c l).toAlgebra := by
  letI : Algebra (J c) (LocP c l) := (elimLoc c l).toAlgebra
  set L := Localization.Away (c l)
  have hu : IsUnit (algebraMap B L (c l)) := IsLocalization.Away.algebraMap_isUnit _
  have hinjB : Function.Injective (algebraMap B L) := IsLocalization.injective L
    (powers_le_nonZeroDivisors_of_noZeroDivisors hl)
  have hinj : Function.Injective (elimLoc c l) := elim_injective hl (algebraMap B L) hinjB _ rfl
  have halg : ∀ b : B, algebraMap (J c) (LocP c l) (algebraMap B (J c) b) =
      C (algebraMap B L b) := fun b => elimLoc_algebraMap b
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    simp only [map_pow]
    rw [halg]
    exact (hu.map C).pow n
  · intro z
    induction z using MvPolynomial.induction_on with
    | C a =>
      obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, hb⟩ := IsLocalization.mk'_surjective (Submonoid.powers (c l)) a
      refine ⟨⟨algebraMap B (J c) b, ⟨_, n, rfl⟩⟩, ?_⟩
      simp only [map_pow]
      rw [halg, halg, ← map_pow, ← map_mul, ← hb]
      congr 1
      rw [← map_pow]
      exact IsLocalization.mk'_spec _ _ _
    | add z z' hz hz' =>
      obtain ⟨⟨a, s⟩, ha⟩ := hz
      obtain ⟨⟨a', s'⟩, ha'⟩ := hz'
      refine ⟨⟨a * s' + a' * s, s * s'⟩, ?_⟩
      simp only [Submonoid.coe_mul, map_mul, map_add] at ha ha' ⊢
      rw [← ha, ← ha']; ring
    | mul_X z j hz =>
      obtain ⟨⟨a, s⟩, ha⟩ := hz
      refine ⟨⟨a * σ c (l.succAbove j), s⟩, ?_⟩
      simp only [map_mul] at ha ⊢
      have hX : algebraMap (J c) (LocP c l) (σ c (l.succAbove j)) = X j := elimLoc_σ j
      rw [hX, ← ha]; ring
  · intro x y hxy
    exact ⟨1, by rw [hinj hxy]⟩

end Away

section Quot

variable (c : Fin r → B) (b : B)

/-- Reduction of the Jouanolou ring modulo `b ∈ B`. -/
def redHom : J c →+* J (Ideal.Quotient.mk (Ideal.span {b}) ∘ c) :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (MvPolynomial.map (Ideal.Quotient.mk _)))
    (fun a ha => by
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [RingHom.comp_apply, map_mul, map_rel, map_mul, Ideal.Quotient.eq_zero_iff_mem.2
        (Ideal.mem_span_singleton_self _), mul_zero])

lemma redHom_surjective : Function.Surjective (redHom c b) := by
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective p
  exact ⟨Ideal.Quotient.mk _ q, rfl⟩

lemma ker_redHom : RingHom.ker (redHom c b) = Ideal.span {algebraMap B (J c) b} := by
  apply le_antisymm
  · intro z hz
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [RingHom.mem_ker] at hz
    change Ideal.Quotient.mk _ (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {b})) p) = 0 at hz
    rw [Ideal.Quotient.eq_zero_iff_mem] at hz
    obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 hz
    obtain ⟨a, rfl⟩ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective a'
    rw [← map_rel, ← map_mul, ← sub_eq_zero, ← map_sub] at ha'
    have hk : p - a * rel c ∈ Ideal.map (C : B →+* MvPolynomial (Fin r) B)
        (RingHom.ker (Ideal.Quotient.mk (Ideal.span {b}))) := by
      rw [← MvPolynomial.ker_map, RingHom.mem_ker]
      rw [← neg_sub, map_neg, ha', neg_zero]
    rw [Ideal.mk_ker, Ideal.map_span, Set.image_singleton] at hk
    obtain ⟨p', hp'⟩ := Ideal.mem_span_singleton'.1 hk
    have : (Ideal.Quotient.mk (Ideal.span {rel c}) p) =
        Ideal.Quotient.mk _ p' * algebraMap B (J c) b := by
      rw [IsScalarTower.algebraMap_apply B (MvPolynomial (Fin r) B), MvPolynomial.algebraMap_eq,
        Ideal.Quotient.algebraMap_eq, ← map_mul, hp', Ideal.Quotient.eq]
      rw [show p - (p - a * rel c) = a * rel c by ring]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      IsScalarTower.algebraMap_apply B (MvPolynomial (Fin r) B), MvPolynomial.algebraMap_eq,
      Ideal.Quotient.algebraMap_eq]
    change Ideal.Quotient.mk _ (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {b})) (C b)) = 0
    rw [map_C, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self b), C_0, map_zero]

/-- `J(c)/(b) ≅ J(c mod b)`. -/
def quotEquiv : J c ⧸ Ideal.span {algebraMap B (J c) b} ≃+* J (Ideal.Quotient.mk (Ideal.span {b}) ∘ c) :=
  (Ideal.quotEquivOfEq (ker_redHom c b).symm).trans
    (RingHom.quotientKerEquivOfSurjective (redHom_surjective c b))

end Quot

section UFD

variable {c : Fin (r + 1) → B} {l : Fin (r + 1)}

/-- The image of `B` in the Jouanolou ring (injective over a domain). -/
lemma algebraMap_injective [IsDomain B] (hl : c l ≠ 0) :
    Function.Injective (algebraMap B (J c)) := by
  set L := Localization.Away (c l)
  have hinjB : Function.Injective (algebraMap B L) := IsLocalization.injective L
    (powers_le_nonZeroDivisors_of_noZeroDivisors hl)
  intro a a' h
  have h2 := congrArg (elimLoc c l) h
  rw [elimLoc_algebraMap, elimLoc_algebraMap] at h2
  exact hinjB (C_injective _ _ h2)

/-- **The Jouanolou ring over a UFD is a UFD** when `c_l` is prime and does not divide some
`c_m`. -/
theorem ufd [IsDomain B] [IsNoetherianRing B] [UniqueFactorizationMonoid B] (hl : Prime (c l))
    {m : Fin (r + 1)} (hm : ¬ c l ∣ c m) : UniqueFactorizationMonoid (J c) := by
  have hl0 := hl.ne_zero
  haveI := isDomain hl0
  set L := Localization.Away (c l)
  haveI : IsDomain L := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors hl0)
  haveI : UniqueFactorizationMonoid L :=
    BezoutCounterexample.UniqueFactorizationMonoid.of_isLocalization (Submonoid.powers (c l))
      (fun h => hl0 (by obtain ⟨n, hn⟩ := h; exact pow_eq_zero_iff'.1 hn |>.1)) L
  letI : Algebra (J c) (LocP c l) := (elimLoc c l).toAlgebra
  haveI : IsLocalization.Away (algebraMap B (J c) (c l)) (LocP c l) := isLocalization_elim hl0
  -- `c_l` is prime in `J c`
  have hprime : Prime (algebraMap B (J c) (c l)) := by
    have hne : algebraMap B (J c) (c l) ≠ 0 := fun h =>
      hl0 (algebraMap_injective hl0 (by rw [h, map_zero]))
    rw [← Ideal.span_singleton_prime hne]
    haveI : IsDomain (B ⧸ Ideal.span {c l}) :=
      (Ideal.Quotient.isDomain_iff_prime _).2 ((Ideal.span_singleton_prime hl0).2 hl)
    have hm' : (Ideal.Quotient.mk (Ideal.span {c l}) ∘ c) m ≠ 0 := by
      simp only [Function.comp_apply, ne_eq, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton]
      exact hm
    haveI := isDomain hm'
    rw [← Ideal.Quotient.isDomain_iff_prime]
    exact (quotEquiv c (c l)).toMulEquiv.isDomain_iff.2 inferInstance
  exact BezoutCounterexample.UniqueFactorizationMonoid.of_isLocalization_away hprime (LocP c l)

end UFD

end BezoutCounterexample.Jou


namespace BezoutCounterexample

open TrivSqZeroExt

section DerivOfTsze

variable {S : Type*} [CommRing S] [Algebra ℚ S]

/-- A ring hom `θ : S → S ⊕ εS` with `fst ∘ θ = id` gives a derivation (`snd ∘ θ`). -/
def derivOfTsze (θ : S →+* TrivSqZeroExt S S) (hfst : ∀ s, (θ s).fst = s) : Derivation ℚ S S where
  toFun s := (θ s).snd
  map_add' s t := by simp
  map_smul' q s := by
    change (θ (q • s)).snd = q • (θ s).snd
    rw [Algebra.smul_def, map_mul, snd_mul, hfst, smul_eq_mul]
    have h0 : θ (algebraMap ℚ S q) = algebraMap ℚ (TrivSqZeroExt S S) q := by
      have : (θ.comp (algebraMap ℚ S)) = algebraMap ℚ (TrivSqZeroExt S S) := RingHom.ext_rat _ _
      exact congrArg (fun f : ℚ →+* _ => f q) this
    have h1 : ((algebraMap ℚ (TrivSqZeroExt S S)) q).snd = 0 := rfl
    rw [h0]
    simp [Algebra.smul_def, h1]
  map_one_eq_zero' := by
    change (θ 1).snd = 0
    rw [map_one, snd_one]
  leibniz' s t := by
    change (θ (s * t)).snd = s • (θ t).snd + t • (θ s).snd
    rw [map_mul, snd_mul, hfst, hfst]
    simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    ring

@[simp] lemma derivOfTsze_apply (θ : S →+* TrivSqZeroExt S S) (hfst : ∀ s, (θ s).fst = s) (s : S) :
    derivOfTsze θ hfst s = (θ s).snd := rfl

end DerivOfTsze

namespace Jou

open MvPolynomial

variable {B : Type*} [CommRing B] [Algebra ℚ B] {r : ℕ} (c : Fin r → B)

/-- The coefficient map `b ↦ b + ε δ(b)` into the square-zero extension of `J c`. -/
def coefTsze (δ : Derivation ℚ B B) : B →+* TrivSqZeroExt (J c) (J c) where
  toFun b := inl (algebraMap B (J c) b) + inr (algebraMap B (J c) (δ b))
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp only [snd_mul, fst_add, fst_inl, fst_inr, add_zero, snd_add, snd_inl, snd_inr,
        zero_add, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]; ring
  map_zero' := by ext <;> simp
  map_add' a b := by
    ext
    · simp only [fst_add, fst_inl, fst_inr, add_zero, map_add]
    · simp only [snd_add, snd_inl, snd_inr, zero_add, map_add]

/-- The ring hom `B[σ] → J ⊕ εJ` extending `δ` with `σᵢ ↦ σᵢ + ε vᵢ`. -/
def polyTsze (δ : Derivation ℚ B B) (v : Fin r → J c) :
    MvPolynomial (Fin r) B →+* TrivSqZeroExt (J c) (J c) :=
  eval₂Hom (coefTsze c δ) (fun i => inl (σ c i) + inr (v i))

set_option synthInstance.maxHeartbeats 200000 in
lemma fst_polyTsze (δ : Derivation ℚ B B) (v : Fin r → J c) (p : MvPolynomial (Fin r) B) :
    (polyTsze c δ v p).fst = mk c p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [polyTsze, coefTsze, mk_C]
  | add p q hp hq => rw [map_add, fst_add, hp, hq, map_add]
  | mul_X p i hp => rw [map_mul, fst_mul, hp, map_mul]; simp [polyTsze, σ]

variable {c}

set_option synthInstance.maxHeartbeats 200000 in
/-- **Lifting a derivation** of `B` to the Jouanolou ring, with prescribed values on `σ`. -/
def liftDer (δ : Derivation ℚ B B) (v : Fin r → J c)
    (hv : ∑ i, (σ c i * algebraMap B (J c) (δ (c i)) + algebraMap B (J c) (c i) * v i) = 0) :
    Derivation ℚ (J c) (J c) :=
  derivOfTsze (Ideal.Quotient.lift _ (polyTsze c δ v) (fun a ha => by
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [RingHom.map_mul (polyTsze c δ v)]
      have : polyTsze c δ v (rel c) = 0 := by
        ext
        · rw [fst_polyTsze, mk_rel, fst_zero]
        · simp only [rel, map_sub, map_sum, map_mul, map_one, snd_sub, snd_one, sub_zero, snd_sum,
            snd_zero]
          rw [← hv]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [polyTsze, eval₂Hom_X', eval₂Hom_C, coefTsze, RingHom.coe_mk, MonoidHom.coe_mk,
            OneHom.coe_mk, snd_mul, fst_add, fst_inl, fst_inr, add_zero, snd_add, snd_inl, snd_inr,
            zero_add, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
          ring
      rw [this, mul_zero]))
    (fun s => by
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective s
      rw [Ideal.Quotient.lift_mk, fst_polyTsze]; rfl)

lemma liftDer_algebraMap (δ : Derivation ℚ B B) (v : Fin r → J c) (hv) (b : B) :
    liftDer δ v hv (algebraMap B (J c) b) = algebraMap B (J c) (δ b) := by
  have : algebraMap B (J c) b = Ideal.Quotient.mk _ (C b) := by
    rw [IsScalarTower.algebraMap_apply B (MvPolynomial (Fin r) B), MvPolynomial.algebraMap_eq,
      Ideal.Quotient.algebraMap_eq]
  rw [liftDer, derivOfTsze_apply, this, Ideal.Quotient.lift_mk]
  simp [polyTsze, coefTsze, Algebra.algebraMap_eq_smul_one]

lemma liftDer_σ (δ : Derivation ℚ B B) (v : Fin r → J c) (hv) (i : Fin r) :
    liftDer δ v hv (σ c i) = v i := by
  rw [liftDer, derivOfTsze_apply, σ, mk, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.lift_mk]
  simp [polyTsze]

end Jou

end BezoutCounterexample


namespace BezoutCounterexample.Jou

open MvPolynomial

variable {B : Type*} [CommRing B] {r : ℕ}

section Map

variable {B' : Type*} [CommRing B'] (f : B →+* B') (c : Fin r → B)

/-- Functoriality of the Jouanolou ring in the base. -/
def map : J c →+* J (f ∘ c) :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (MvPolynomial.map f)) (fun a ha => by
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [RingHom.comp_apply, map_mul, map_rel, map_mul,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), mul_zero])

lemma map_mk (p : MvPolynomial (Fin r) B) :
    map f c (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (MvPolynomial.map f p) := rfl

lemma map_algebraMap (b : B) : map f c (algebraMap B (J c) b) = algebraMap B' (J (f ∘ c)) (f b) := by
  rw [IsScalarTower.algebraMap_apply B (MvPolynomial (Fin r) B), MvPolynomial.algebraMap_eq,
    Ideal.Quotient.algebraMap_eq, map_mk, map_C, IsScalarTower.algebraMap_apply B' (MvPolynomial (Fin r) B'),
    MvPolynomial.algebraMap_eq, Ideal.Quotient.algebraMap_eq]

lemma map_σ (i : Fin r) : map f c (σ c i) = σ (f ∘ c) i := by
  simp [σ, map_mk]

/-- Clearing denominators of a polynomial over a localization. -/
lemma exists_clear (M : Submonoid B) [Algebra B B'] [IsLocalization M B'] (p : MvPolynomial (Fin r) B') :
    ∃ (q : MvPolynomial (Fin r) B) (m : M),
      MvPolynomial.map (algebraMap B B') q = C (algebraMap B B' m) * p := by
  letI := MvPolynomial.algebraMvPolynomial (σ := Fin r) (R := B) (S := B')
  obtain ⟨⟨q, ⟨_, m, hm, rfl⟩⟩, hq⟩ := IsLocalization.surj (M.map (C (σ := Fin r))) p
  refine ⟨q, ⟨m, hm⟩, ?_⟩
  simp only [MvPolynomial.algebraMap_def, map_C] at hq
  rw [← hq, mul_comm]

/-- Polynomials killed by the localization map are killed by an element of `M`. -/
lemma exists_kill (M : Submonoid B) [Algebra B B'] [IsLocalization M B'] {g : MvPolynomial (Fin r) B}
    (hg : MvPolynomial.map (algebraMap B B') g = 0) : ∃ m : M, C (m : B) * g = 0 := by
  letI := MvPolynomial.algebraMvPolynomial (σ := Fin r) (R := B) (S := B')
  have : algebraMap (MvPolynomial (Fin r) B) (MvPolynomial (Fin r) B') g = 0 := by
    rw [MvPolynomial.algebraMap_def]; exact hg
  obtain ⟨⟨_, m, hm, rfl⟩, h⟩ := (IsLocalization.map_eq_zero_iff (M.map (C (σ := Fin r))) _ g).1 this
  exact ⟨⟨m, hm⟩, h⟩

/-- **Base change to a localization.** -/
theorem isLocalization_map (M : Submonoid B) [Algebra B B'] [IsLocalization M B'] :
    @IsLocalization _ _ (M.map (algebraMap B (J c))) (J (algebraMap B B' ∘ c)) _
      (map (algebraMap B B') c).toAlgebra := by
  letI : Algebra (J c) (J (algebraMap B B' ∘ c)) := (map (algebraMap B B') c).toAlgebra
  have hmap : ∀ z : J c, algebraMap (J c) (J (algebraMap B B' ∘ c)) z = map (algebraMap B B') c z :=
    fun _ => rfl
  have hJC : ∀ b : B, algebraMap B (J c) b = Ideal.Quotient.mk _ (C b) := fun b => by
    rw [IsScalarTower.algebraMap_apply B (MvPolynomial (Fin r) B), MvPolynomial.algebraMap_eq,
      Ideal.Quotient.algebraMap_eq]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, ⟨m, hm, rfl⟩⟩
    rw [hmap, map_algebraMap]
    exact (IsLocalization.map_units B' ⟨m, hm⟩).map _
  · intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨q, m, hq⟩ := exists_clear M p
    refine ⟨⟨Ideal.Quotient.mk _ q, ⟨algebraMap B (J c) m, ⟨m, m.2, rfl⟩⟩⟩, ?_⟩
    simp only
    rw [hmap, hmap, map_mk, map_algebraMap, hq, IsScalarTower.algebraMap_apply B' (MvPolynomial (Fin r) B'),
      MvPolynomial.algebraMap_eq, Ideal.Quotient.algebraMap_eq, map_mul, mul_comm]
  · intro z z' h
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨p', rfl⟩ := Ideal.Quotient.mk_surjective z'
    rw [hmap, hmap, map_mk, map_mk, Ideal.Quotient.eq, ← map_sub] at h
    obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 h
    obtain ⟨a, m, ha⟩ := exists_clear M a'
    have hk : MvPolynomial.map (algebraMap B B') (C (m : B) * (p - p') - a * rel c) = 0 := by
      rw [map_sub, map_mul, map_mul, map_C, ha, map_rel, ← ha']
      ring
    obtain ⟨m', hm'⟩ := exists_kill M hk
    refine ⟨⟨algebraMap B (J c) (m' * m), ⟨m' * m, (m' * m).2, rfl⟩⟩, ?_⟩
    simp only
    rw [← sub_eq_zero, ← mul_sub, hJC, ← map_sub, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    have : C ((m' : B) * m) * (p - p') = (C (m' : B) * a) * rel c := by
      rw [C_mul]
      linear_combination hm'
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end Map

section Unit

variable {c : Fin (r + 1) → B} {l : Fin (r + 1)}

/-- If `c_l` is a unit, the Jouanolou ring is a polynomial ring. -/
def equivPoly [IsDomain B] (u : Bˣ) (hu : c l = u) : J c ≃+* MvPolynomial (Fin r) B :=
  RingEquiv.ofBijective (elim (RingHom.id B) u hu)
    ⟨elim_injective (by rw [hu]; exact u.ne_zero) (RingHom.id B) Function.injective_id u hu, by
      intro z
      induction z using MvPolynomial.induction_on with
      | C a => exact ⟨algebraMap B (J c) a, by rw [elim_algebraMap]; rfl⟩
      | add p q hp hq =>
        obtain ⟨x, hx⟩ := hp; obtain ⟨y, hy⟩ := hq
        exact ⟨x + y, by rw [map_add, hx, hy]⟩
      | mul_X p j hp =>
        obtain ⟨x, hx⟩ := hp
        exact ⟨x * σ c (l.succAbove j), by rw [map_mul, hx, elim_σ]⟩⟩

lemma equivPoly_apply [IsDomain B] (u : Bˣ) (hu : c l = u) (z : J c) :
    equivPoly u hu z = elim (RingHom.id B) u hu z := rfl

lemma equivPoly_algebraMap [IsDomain B] (u : Bˣ) (hu : c l = u) (b : B) :
    equivPoly u hu (algebraMap B (J c) b) = C b := by
  rw [equivPoly_apply, elim_algebraMap]; rfl

lemma equivPoly_σ [IsDomain B] (u : Bˣ) (hu : c l = u) (j : Fin r) :
    equivPoly u hu (σ c (l.succAbove j)) = X j := by
  rw [equivPoly_apply, elim_σ]

end Unit

end BezoutCounterexample.Jou


namespace BezoutCounterexample.Jou

open MvPolynomial

variable {B : Type*} [CommRing B] {r : ℕ}

/-- **The Jouanolou ring is formally smooth over its base** (Jacobian criterion with the Euler
derivation `∑ σᵢ ∂/∂σᵢ`, which maps the relation `q` to `q + 1`). -/
theorem formallySmooth (c : Fin r → B) : Algebra.FormallySmooth B (J c) := by
  set P := MvPolynomial (Fin r) B
  have hrange : Ideal.span (Set.range fun _ : Fin 1 => rel c) = Ideal.span {rel c} := by
    rw [Set.range_const]
  set E : Derivation B P P := MvPolynomial.mkDerivation B (fun i => (X i : P)) with hE
  have hErel : E (rel c) = rel c + 1 := by
    rw [rel, map_sub, map_sum, Derivation.map_one_eq_zero, sub_zero, sub_add_cancel]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Derivation.leibniz, hE, MvPolynomial.mkDerivation_X, MvPolynomial.derivation_C,
      smul_zero, zero_add, smul_eq_mul, mul_comm]
  let D : Fin 1 → Derivation B P (P ⧸ Ideal.span (Set.range fun _ : Fin 1 => rel c)) := fun _ =>
    ((Ideal.Quotient.mkₐ P (Ideal.span (Set.range fun _ : Fin 1 => rel c))).toLinearMap).compDer E
  have hD : ∀ i j, D i ((fun _ : Fin 1 => rel c) j) = if i = j then 1 else 0 := by
    intro i j
    have hij : i = j := Subsingleton.elim i j
    rw [if_pos hij]
    show Ideal.Quotient.mk _ (E (rel c)) = 1
    rw [hErel, map_add, Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.subset_span (Set.mem_range_self (0 : Fin 1))), zero_add, map_one]
  haveI := Principalization.formallySmooth_quotient_of_dual (R := B) (fun _ : Fin 1 => rel c) D hD
  exact Algebra.FormallySmooth.of_equiv (Ideal.quotientEquivAlgOfEq B hrange)

end BezoutCounterexample.Jou

