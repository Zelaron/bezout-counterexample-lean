import BezoutCounterexample.Principalization.Drop
import BezoutCounterexample.Jouanolou

/-!
# The Jouanolou torsor over the weighted Rees algebra

Lemma 4.2 (`lem:torsor`) of the paper.

We define the torsor `U = J(y)` over the Rees algebra `R` of the component filtration,
where `y` consists of `πT` and the positive-degree generators, and prove that `U` is a smooth
finite-type ℚ-domain in which `s = T⁻¹` is prime, and that `U` is a UFD.
-/

noncomputable section


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) (d : ℕ)

/-- The pairs `(j, g)` indexing the positive-degree generators. -/
def genPairs : List (ℤ × A) :=
  ((Finset.Icc (1 : ℤ) d).toList).flatMap fun j => (gensF hI hmax h𝔭 d j).toList.map fun g => (j, g)

lemma genPairs_mem {p : ℤ × A} (hp : p ∈ genPairs hI hmax h𝔭 d) :
    1 ≤ p.1 ∧ p.1 ≤ d ∧ p.2 ∈ gensF hI hmax h𝔭 d p.1 := by
  simp only [genPairs, List.mem_flatMap, Finset.mem_toList, Finset.mem_Icc, List.mem_map] at hp
  obtain ⟨j, ⟨hj1, hjd⟩, g, hg, rfl⟩ := hp
  exact ⟨hj1, hjd, hg⟩

lemma mem_genPairs {j : ℤ} (hj1 : 1 ≤ j) (hjd : j ≤ d) {g : A} (hg : g ∈ gensF hI hmax h𝔭 d j) :
    (j, g) ∈ genPairs hI hmax h𝔭 d := by
  simp only [genPairs, List.mem_flatMap, Finset.mem_toList, Finset.mem_Icc, List.mem_map]
  exact ⟨j, ⟨hj1, hjd⟩, g, hg, rfl⟩

/-- The number of positive-degree generators. -/
abbrev nGen : ℕ := (genPairs hI hmax h𝔭 d).length

/-- The degrees of the torsor generators (`0` indexes `π T`). -/
def genDeg : Fin (nGen hI hmax h𝔭 d + 1) → ℤ :=
  Fin.cons 1 fun i => ((genPairs hI hmax h𝔭 d).get i).1

/-- The coefficients of the torsor generators. -/
def genCoeff (π : A) : Fin (nGen hI hmax h𝔭 d + 1) → A :=
  Fin.cons π fun i => ((genPairs hI hmax h𝔭 d).get i).2

lemma genDeg_pos (i : Fin (nGen hI hmax h𝔭 d + 1)) : 1 ≤ genDeg hI hmax h𝔭 d i := by
  cases i using Fin.cases with
  | zero => simp [genDeg]
  | succ i => simp only [genDeg, Fin.cons_succ]; exact (genPairs_mem hI hmax h𝔭 d (List.get_mem (genPairs hI hmax h𝔭 d) i)).1

lemma genDeg_le (hd : 1 ≤ d) (i : Fin (nGen hI hmax h𝔭 d + 1)) : genDeg hI hmax h𝔭 d i ≤ d := by
  cases i using Fin.cases with
  | zero => simp [genDeg]; exact_mod_cast hd
  | succ i => simp only [genDeg, Fin.cons_succ]; exact (genPairs_mem hI hmax h𝔭 d (List.get_mem (genPairs hI hmax h𝔭 d) i)).2.1

lemma genCoeff_mem {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1) (i : Fin (nGen hI hmax h𝔭 d + 1)) :
    genCoeff hI hmax h𝔭 d π i ∈ (compFil hI hmax h𝔭 d).F (genDeg hI hmax h𝔭 d i) := by
  cases i using Fin.cases with
  | zero => simpa [genCoeff, genDeg] using hπ
  | succ i =>
    simp only [genCoeff, genDeg, Fin.cons_succ]
    have := (genPairs_mem hI hmax h𝔭 d (List.get_mem (genPairs hI hmax h𝔭 d) i)).2.2
    rw [← span_gensF]; exact Ideal.subset_span this

/-- **The torsor generators** `y₀ = π T`, `y_{i+1} = gᵢ T^{jᵢ}`. -/
def torsorY {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1) :
    Fin (nGen hI hmax h𝔭 d + 1) → ReesAlg (compFil hI hmax h𝔭 d) := fun i =>
  ⟨LaurentPolynomial.C (genCoeff hI hmax h𝔭 d π i) * T (genDeg hI hmax h𝔭 d i),
    C_mul_T_mem_ReesAlg (genCoeff_mem hI hmax h𝔭 d hπ i)⟩

/-- **The torsor** `U = R[σ]/(∑ σᵢ yᵢ - 1)`. -/
abbrev Torsor {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1) :=
  Jou.J (torsorY hI hmax h𝔭 d hπ)

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

include hπ0 in
lemma torsorY_zero_ne : torsorY hI hmax h𝔭 d hπ 0 ≠ 0 := by
  intro h
  have := congrArg (fun p : ReesAlg (compFil hI hmax h𝔭 d) => (p : A[T;T⁻¹]).coeff 1) h
  simp only [torsorY, genCoeff, genDeg, Fin.cons_zero, coeff_C_mul_T] at this
  exact hπ0 (by simpa using this)

include hπ0 in
theorem torsor_isDomain : IsDomain (Torsor hI hmax h𝔭 d hπ) :=
  Jou.isDomain (torsorY_zero_ne hI hmax h𝔭 hπ hπ0)

omit [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
omit [IsDomain A] [Algebra ℚ A] in
lemma rees_algebraMap_injective (Φ : WFil A) : Function.Injective (algebraMap A (ReesAlg Φ)) := by
  intro a b h
  have := congrArg (fun p : ReesAlg Φ => (p : A[T;T⁻¹]).coeff 0) h
  simp only [Subalgebra.coe_algebraMap, ← LaurentPolynomial.C_eq_algebraMap,
    LaurentPolynomial.C_apply] at this
  exact this

include hπ0 in
theorem torsor_injective :
    Function.Injective (algebraMap A (Torsor hI hmax h𝔭 d hπ)) := by
  rw [IsScalarTower.algebraMap_eq A (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ)]
  exact (Jou.algebraMap_injective (torsorY_zero_ne hI hmax h𝔭 hπ hπ0)).comp
    (rees_algebraMap_injective _)

end BezoutCounterexample.Principalization

namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)
include hd hw

theorem torsor_finiteType : Algebra.FiniteType ℚ (Torsor hI hmax h𝔭 d hπ) := by
  have := reesAlg_finiteType hI hmax h𝔭 d hd hw
  have : Algebra.FiniteType ℚ (ReesAlg (compFil hI hmax h𝔭 d)) :=
    Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have : Algebra.FiniteType (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ) :=
    inferInstance
  exact Algebra.FiniteType.trans (S := ReesAlg (compFil hI hmax h𝔭 d)) inferInstance inferInstance

include hI hmax h𝔭 in
/-- **The torsor is smooth over `ℚ`.** -/
theorem torsor_smooth : Algebra.Smooth ℚ (Torsor hI hmax h𝔭 d hπ) := by
  have := rees_smooth hI hmax h𝔭 hd hw
  have := Jou.formallySmooth (torsorY hI hmax h𝔭 d hπ)
  have := torsor_finiteType hI hmax h𝔭 hd hw hπ
  refine ⟨Algebra.FormallySmooth.comp ℚ (ReesAlg (compFil hI hmax h𝔭 d)) _, ?_⟩
  exact Algebra.FinitePresentation.of_finiteType.1 inferInstance

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

section LaurentPrime

variable {B : Type*} [CommRing B] [Algebra ℚ B] [IsDomain B]

/-- Reduction of Laurent polynomials modulo `b`. -/
abbrev lred (b : B) : B[T;T⁻¹] →+* (B ⧸ Ideal.span {b})[T;T⁻¹] := lmap (Ideal.Quotient.mk _)

omit [IsDomain B] [Algebra ℚ B] in
lemma ker_lred (b : B) : RingHom.ker (lred b) = Ideal.span {LaurentPolynomial.C b} := by
  classical
  apply le_antisymm
  · intro p hp
    rw [RingHom.mem_ker] at hp
    have hco : ∀ j, ∃ q : B, p.coeff j = b * q := by
      intro j
      have h1 : (lred b p).coeff j = 0 := by rw [hp]; rfl
      rw [lmap_coeff, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h1
      obtain ⟨q, hq⟩ := h1
      exact ⟨q, hq⟩
    choose q hq using hco
    set Q : B[T;T⁻¹] := ∑ j ∈ p.coeff.support, LaurentPolynomial.C (q j) * T j
    refine Ideal.mem_span_singleton'.2 ⟨Q, ?_⟩
    ext j
    rw [mul_comm, coeff_C_mul', laurent_coeff_sum]
    simp_rw [coeff_C_mul_T]
    rw [Finset.sum_ite_eq]
    split_ifs with hj
    · rw [hq]
    · rw [Finsupp.notMem_support_iff.1 hj, mul_zero]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    ext j
    rw [lmap_coeff, LaurentPolynomial.C_apply]
    split_ifs
    · simp
    · simp

omit [IsDomain B] [Algebra ℚ B] in
/-- A prime of `B` stays prime in `B[T^±]`. -/
theorem prime_C_laurent {b : B} (hb : Prime b) : Prime (LaurentPolynomial.C b : B[T;T⁻¹]) := by
  have hb0 : (LaurentPolynomial.C b : B[T;T⁻¹]) ≠ 0 := by
    intro h
    have := congrArg (fun r : B[T;T⁻¹] => r.coeff 0) h
    simp [LaurentPolynomial.C_apply] at this
    exact hb.ne_zero this
  rw [← Ideal.span_singleton_prime hb0, ← ker_lred]
  have : IsDomain (B ⧸ Ideal.span {b}) :=
    (Ideal.Quotient.isDomain_iff_prime _).2 ((Ideal.span_singleton_prime hb.ne_zero).2 hb)
  exact RingHom.ker_isPrime _

end LaurentPrime

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

/-- Two coordinates of a centred chart do not lie in a common principal ideal. -/
lemma Chart.not_two_mem_span {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] {n : ℕ}
    (c : Chart S n) (hc : c.IsCentred) {i j : Fin n} (hij : i ≠ j) {g : S}
    (hg : g ∈ maximalIdeal S) (hi : c.x i ∈ Ideal.span {g}) (hj : c.x j ∈ Ideal.span {g}) : False := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hi
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hj
  -- `a` is a unit
  have h1 : c.d i (c.x i) = 1 := c.d_x_self i
  rw [← ha, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1
  have hau : IsUnit a := by
    by_contra hna
    have hmem : a * c.d i g + g * c.d i a ∈ maximalIdeal S :=
      Ideal.add_mem _ (Ideal.mul_mem_right _ _ ((mem_maximalIdeal a).2 hna))
        (Ideal.mul_mem_right _ _ hg)
    rw [h1] at hmem
    exact (maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).2 hmem)
  obtain ⟨u, rfl⟩ := hau
  have hg' : g = ↑u⁻¹ * c.x i := by rw [← ha, ← mul_assoc, Units.inv_mul, one_mul]
  have hxj : c.x j = (b * ↑u⁻¹) * c.x i := by rw [← hb, hg']; ring
  have h2 : c.d j (c.x j) = 1 := c.d_x_self j
  rw [hxj, Derivation.leibniz, smul_eq_mul, smul_eq_mul, c.d_x_ne (Ne.symm hij), mul_zero,
    zero_add] at h2
  have hmem : c.x i * c.d j (b * ↑u⁻¹) ∈ maximalIdeal S := Ideal.mul_mem_right _ _ (hc.x_mem i)
  rw [h2] at hmem
  exact (maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).2 hmem)

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
include hI hmax h𝔭 hd hw

/-- **Non-divisorial centres are not principal**: some generator of `F₁ = 𝔭` is not divisible by a
given `π ∈ 𝔭`. -/
theorem exists_gen_not_dvd (hk2 : v₀ 1 ≠ 0) {π : A} (hπ : π ∈ 𝔭) :
    ∃ g ∈ gensF hI hmax h𝔭 d 1, ¬ π ∣ g := by
  by_contra hall
  push Not at hall
  have hle : 𝔭 ≤ Ideal.span {π} := by
    have h1 : (compFil hI hmax h𝔭 d).F 1 = 𝔭 := by
      rw [compFil_F, show ((1 : ℤ) : ℚ) / d = 1 / d by push_cast; ring,
        compF_one_div hI hmax h𝔭 hd hw]
    rw [← h1, ← span_gensF, Ideal.span_le]
    intro g hg
    exact Ideal.mem_span_singleton.2 (hall g hg)
  have := h𝔭.1.1
  obtain ⟨𝔪, h𝔪, h𝔭𝔪⟩ := Ideal.exists_le_maximal 𝔭 (Ideal.IsPrime.ne_top ‹_›)
  have := h𝔪
  have hZ := mem_maxLocus_of_minimal hI hmax h𝔭 𝔪 h𝔭𝔪
  obtain ⟨D⟩ := LocData.nonempty hI 𝔪 hZ.1 hZ.2
  have hp : 𝔭 = D.p := D.eq_p_of_minimal h𝔭 h𝔭𝔪
  -- `1 < k`
  have hn : 1 < D.n := by
    by_contra h
    apply hk2
    rw [← D.hv]
    simp only [ext0]; rw [dite_eq_right (by omega)]
  have hk : 1 < D.k := by
    have := (D.supp ⟨1, hn⟩).1 (by
      have := congrFun D.hv 1
      rw [show (1 : ℕ) = ((⟨1, hn⟩ : Fin D.n) : ℕ) from rfl, ext0_apply] at this
      rw [this]; exact hk2)
    simpa using this
  set c := Loc.transport (D.ctrl 𝔪 D.hg) D.ck
  have hPle : D.P ≤ Ideal.span {algebraMap A (Localization.AtPrime 𝔪) π} := by
    rw [← D.map_p, ← hp]
    refine (Ideal.map_mono hle).trans ?_
    rw [Ideal.map_span, Set.image_singleton]
  have hπm : algebraMap A (Localization.AtPrime 𝔪) π ∈ maximalIdeal (Localization.AtPrime 𝔪) := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ 𝔪]; exact h𝔭𝔪 hπ
  exact c.not_two_mem_span D.cent (i := ⟨0, by omega⟩) (j := ⟨1, hn⟩) (by simp) hπm
    (hPle (Ideal.subset_span ⟨⟨0, by omega⟩, by simp; omega, rfl⟩))
    (hPle (Ideal.subset_span ⟨⟨1, hn⟩, by simpa using hk, rfl⟩))

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial MvPowerSeries

/-- A chart coordinate is not in the next weighted ideal. -/
lemma Chart.IsCentred.x_not_mem_RF {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S]
    [IsNoetherianRing S] {n : ℕ} {c : Chart S n} (hc : c.IsCentred) {e : Fin n → ℚ}
    (he : ∀ i, 0 ≤ e i) (i : Fin n) {t : ℚ} (ht : e i < t) : c.x i ∉ c.RF e t := by
  intro hmem
  rw [hc.mem_RF_iff he] at hmem
  have := hmem (Finsupp.single i 1) (by rw [lam_single]; simpa using ht)
  rw [Chart.coeff_tau, Chart.Dv_single_one, c.d_x_self, map_one] at this
  exact one_ne_zero this

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
include hI hmax h𝔭 hd hw

omit hd hw in
lemma VertexData.k_pos {𝔪 : Ideal A} [𝔪.IsMaximal]
    (D : VertexData hI hmax h𝔭 (d := d) (v₀ := v₀) 𝔪) : 0 < D.k := by
  by_contra h
  push Not at h
  have hz : ∀ i, D.J.e i = 0 := fun i => by
    by_contra hne; have := (D.hsupp i).1 hne; omega
  have hbot : D.J.RF 1 = ⊥ := by
    rw [MC.RF, Chart.RF, Ideal.span_eq_bot]
    rintro _ ⟨α, h0, hα, rfl⟩
    have : α = 0 := Finsupp.ext fun i => h0 i (hz i)
    subst this
    rw [lam_zero] at hα; norm_num at hα
  exact Iloc_ne_bot hI 𝔪 (eq_bot_iff.2 (D.hadm.trans hbot.le))

/-- **Some generator is not in the next filtration step.** -/
theorem exists_gen_not_mem : ∃ j : ℤ, 1 ≤ j ∧ j ≤ d ∧
    ∃ g ∈ gensF hI hmax h𝔭 d j, g ∉ (compFil hI hmax h𝔭 d).F (j + 1) := by
  have := h𝔭.1.1
  obtain ⟨𝔪, h𝔪, h𝔭𝔪⟩ := Ideal.exists_le_maximal 𝔭 (Ideal.IsPrime.ne_top ‹_›)
  have := h𝔪
  obtain ⟨D⟩ := VertexData.nonempty hI hmax h𝔭 hw 𝔪 h𝔭𝔪
  have hk := D.k_pos
  set i₀ : Fin D.n := ⟨D.k - 1, by have := D.hkn; omega⟩
  have hei : D.J.e i₀ ≠ 0 := (D.hsupp i₀).2 (by simp [i₀]; omega)
  have hpos : 0 < D.J.e i₀ := lt_of_le_of_ne (D.J.nonneg i₀) (Ne.symm hei)
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  set w₀ := D.w i₀
  have hw0 : (w₀ : ℚ) = d * D.J.e i₀ := D.hwe i₀
  have hw1 : 1 ≤ w₀ := by
    have : (0 : ℚ) < w₀ := by rw [hw0]; positivity
    exact_mod_cast this
  have hwd : w₀ ≤ d := by
    have hle := D.hinv.le_one (Iloc_le (le_of_Iloc_le (D.hadm.trans
      (D.J.centred.RF_le_maximalIdeal one_pos)))) i₀
    have : (w₀ : ℚ) ≤ d := by rw [hw0]; nlinarith
    exact_mod_cast this
  refine ⟨w₀, by exact_mod_cast hw1, by exact_mod_cast hwd, ?_⟩
  by_contra hall
  push Not at hall
  have hle : (compFil hI hmax h𝔭 d).F w₀ ≤ (compFil hI hmax h𝔭 d).F (w₀ + 1) := by
    rw [← span_gensF, Ideal.span_le]
    intro g hg; exact hall g hg
  have hle' := Ideal.map_mono (f := algebraMap A (Localization.AtPrime 𝔪)) hle
  change ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime 𝔪)).F w₀ ≤
    ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime 𝔪)).F (w₀ + 1) at hle'
  rw [D.hF, D.hF] at hle'
  have hx : D.J.c.x i₀ ∈ chartFil D.J.c D.J.e d w₀ := by
    show D.J.c.x i₀ ∈ D.J.c.RF D.J.e (((w₀ : ℤ) : ℚ) / d)
    rw [show (((w₀ : ℤ) : ℚ) / d) = D.J.e i₀ by push_cast; rw [hw0]; field_simp]
    exact D.J.c.x_mem_RF D.J.e i₀ hei
  have hx' := hle' hx
  refine D.J.centred.x_not_mem_RF D.J.nonneg i₀ ?_ hx'
  push_cast
  rw [add_div, show (w₀ : ℚ) / d = D.J.e i₀ by rw [hw0]; field_simp]
  linarith [show (0 : ℚ) < 1 / d by positivity]

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)

/-- The index of a generator pair. -/
lemma exists_index {j : ℤ} (hj1 : 1 ≤ j) (hjd : j ≤ d) {g : A} (hg : g ∈ gensF hI hmax h𝔭 d j) :
    ∃ l : Fin (nGen hI hmax h𝔭 d + 1), genDeg hI hmax h𝔭 d l = j ∧ genCoeff hI hmax h𝔭 d π l = g := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.1 (mem_genPairs hI hmax h𝔭 d hj1 hjd hg)
  refine ⟨i.succ, ?_, ?_⟩
  · simp only [genDeg, Fin.cons_succ, hi]
  · simp only [genCoeff, Fin.cons_succ, hi]

include hd hw in
lemma F_one_ne_top : (compFil hI hmax h𝔭 d).F 1 ≠ ⊤ := by
  rw [compFil_F, show ((1 : ℤ) : ℚ) / d = 1 / d by push_cast; ring, compF_one_div hI hmax h𝔭 hd hw]
  exact h𝔭.1.1.ne_top

include hd hw in
/-- **The exceptional divisor of the Rees algebra is prime.** -/
theorem rees_s_prime :
    (Ideal.span {reesS (compFil hI hmax h𝔭 d) (fun _j hj => compFil_F_nonpos hI hmax h𝔭 d hj)}).IsPrime := by
  refine span_s_isPrime _ _ (F_one_ne_top hI hmax h𝔭 hd hw) fun a b x y hx hx1 hy hy1 => ?_
  have := compFil_mul_not_mem hI hmax h𝔭 hd hw hx hx1 hy hy1
  push_cast at this ⊢
  exact this

include hd hw in
/-- **`s` is prime in the torsor.** -/
theorem torsor_s_prime (hπ0 : π ≠ 0) :
    Prime (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ)
      (reesS (compFil hI hmax h𝔭 d) (fun _j hj => compFil_F_nonpos hI hmax h𝔭 d hj))) := by
  set R := ReesAlg (compFil hI hmax h𝔭 d)
  set s := reesS (compFil hI hmax h𝔭 d) (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj)
  have := torsor_isDomain hI hmax h𝔭 hπ hπ0
  have hs0 : algebraMap R (Torsor hI hmax h𝔭 d hπ) s ≠ 0 := by
    intro h
    have hinj := Jou.algebraMap_injective (torsorY_zero_ne hI hmax h𝔭 hπ hπ0)
    have : s = 0 := hinj (by rw [h, map_zero])
    have := congrArg (fun p : R => (p : A[T;T⁻¹]).coeff (-1)) this
    simp [s, reesS_coe] at this
  rw [← Ideal.span_singleton_prime hs0, ← Ideal.Quotient.isDomain_iff_prime]
  have : (Ideal.span {s}).IsPrime := rees_s_prime hI hmax h𝔭 hd hw
  have : IsDomain (R ⧸ Ideal.span {s}) := (Ideal.Quotient.isDomain_iff_prime _).2 inferInstance
  -- a generator not divisible by `s`
  obtain ⟨j, hj1, hjd, g, hg, hgF⟩ := exists_gen_not_mem hI hmax h𝔭 hd hw
  obtain ⟨l, hl1, hl2⟩ := exists_index hI hmax h𝔭 (π := π) hj1 hjd hg
  have hl : (Ideal.Quotient.mk (Ideal.span {s}) ∘ torsorY hI hmax h𝔭 d hπ) l ≠ 0 := by
    simp only [Function.comp_apply, ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    rw [mem_span_s_iff]
    intro hall
    apply hgF
    have := hall j
    simp only [torsorY, hl1, hl2, coeff_C_mul_T] at this
    exact this
  have := Jou.isDomain (c := Ideal.Quotient.mk (Ideal.span {s}) ∘ torsorY hI hmax h𝔭 d hπ) (l := l) hl
  exact (Jou.quotEquiv (torsorY hI hmax h𝔭 d hπ) s).toMulEquiv.isDomain_iff.2 inferInstance

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

section LaurentUFD

variable {B : Type*} [CommRing B] [IsDomain B]

instance laurent_noetherian [IsNoetherianRing B] : IsNoetherianRing B[T;T⁻¹] :=
  IsLocalization.isNoetherianRing (Submonoid.powers (Polynomial.X : Polynomial B)) _ inferInstance

lemma laurent_ufd [UniqueFactorizationMonoid B] : UniqueFactorizationMonoid B[T;T⁻¹] :=
  BezoutCounterexample.UniqueFactorizationMonoid.of_isLocalization
    (Submonoid.powers (Polynomial.X : Polynomial B))
    (fun h => by obtain ⟨n, hn⟩ := h; exact Polynomial.X_ne_zero (pow_eq_zero_iff'.1 hn).1) _

end LaurentUFD

variable [UniqueFactorizationMonoid A]
variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)
include hd hw

set_option maxHeartbeats 2000000 in
/-- **The torsor is factorial** (Nagata's criterion twice: `s` is prime, and `U[1/s]` is a
Jouanolou ring over `A[T^±]` with the prime generator `π T`). -/
theorem torsor_ufd (hk2 : v₀ 1 ≠ 0) (hπp : Prime π) (hπ𝔭 : π ∈ 𝔭) :
    UniqueFactorizationMonoid (Torsor hI hmax h𝔭 d hπ) := by
  set R := ReesAlg (compFil hI hmax h𝔭 d)
  set s := reesS (compFil hI hmax h𝔭 d) (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj)
  set y := torsorY hI hmax h𝔭 d hπ
  have := torsor_isDomain hI hmax h𝔭 hπ hπp.ne_zero
  have : Algebra.FiniteType ℚ (Torsor hI hmax h𝔭 d hπ) := torsor_finiteType hI hmax h𝔭 hd hw hπ
  have : IsNoetherianRing (Torsor hI hmax h𝔭 d hπ) := Algebra.FiniteType.isNoetherianRing ℚ _
  have : IsLocalization.Away s A[T;T⁻¹] := isLocalization_away_s _ _
  -- the Jouanolou ring over `A[T^±]`
  set c : Fin (nGen hI hmax h𝔭 d + 1) → A[T;T⁻¹] := algebraMap R A[T;T⁻¹] ∘ y
  let : Algebra (Torsor hI hmax h𝔭 d hπ) (Jou.J c) := (Jou.map (algebraMap R A[T;T⁻¹]) y).toAlgebra
  have hloc : IsLocalization ((Submonoid.powers s).map (algebraMap R (Jou.J y))) (Jou.J c) :=
    Jou.isLocalization_map y (Submonoid.powers s)
  have : IsLocalization.Away (algebraMap R (Torsor hI hmax h𝔭 d hπ) s) (Jou.J c) := by
    rw [Submonoid.map_powers] at hloc; exact hloc
  have : UniqueFactorizationMonoid A[T;T⁻¹] := laurent_ufd
  -- the prime generator `π T`
  have hc0 : Prime (c 0) := by
    have : c 0 = LaurentPolynomial.C π * T 1 := by
      simp [c, y, torsorY, genCoeff, genDeg]
    rw [this]
    exact (associated_mul_unit_right _ _ (isUnit_T 1)).prime (prime_C_laurent hπp)
  obtain ⟨g, hg, hgπ⟩ := exists_gen_not_dvd hI hmax h𝔭 hd hw hk2 hπ𝔭
  obtain ⟨m, hm1, hm2⟩ := exists_index hI hmax h𝔭 (π := π) le_rfl (by exact_mod_cast hd) hg
  have hnd : ¬ c 0 ∣ c m := by
    have h0 : c 0 = LaurentPolynomial.C π * T 1 := by simp [c, y, torsorY, genCoeff, genDeg]
    have hm : c m = LaurentPolynomial.C g * T 1 := by
      show ((y m : R) : A[T;T⁻¹]) = _
      simp only [y, torsorY, hm1, hm2]
    rw [h0, hm]
    rintro ⟨q, hq⟩
    apply hgπ
    have h1 : LaurentPolynomial.C g = LaurentPolynomial.C π * q := by
      have hT : (T 1 : A[T;T⁻¹]) * T (-1) = 1 := by rw [← T_add]; simp
      calc LaurentPolynomial.C g = LaurentPolynomial.C g * T 1 * T (-1) := by
            rw [mul_assoc, hT, mul_one]
        _ = LaurentPolynomial.C π * T 1 * q * T (-1) := by rw [hq]
        _ = LaurentPolynomial.C π * q * (T 1 * T (-1)) := by ring
        _ = LaurentPolynomial.C π * q := by rw [hT, mul_one]
    have h2 := congrArg (fun p : A[T;T⁻¹] => p.coeff 0) h1
    simp only [LaurentPolynomial.C_apply, coeff_C_mul'] at h2
    exact ⟨q.coeff 0, h2⟩
  have : UniqueFactorizationMonoid (Jou.J c) := Jou.ufd hc0 hnd
  exact BezoutCounterexample.UniqueFactorizationMonoid.of_isLocalization_away
    (torsor_s_prime hI hmax h𝔭 hd hw hπ hπp.ne_zero) (Jou.J c)

end BezoutCounterexample.Principalization

